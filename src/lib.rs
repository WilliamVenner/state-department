#![doc = include_str!("../README.md")]
#![deny(missing_docs)]

use std::{
    any::{Any, TypeId},
    cell::UnsafeCell,
    collections::HashMap,
    marker::PhantomData,
    mem::MaybeUninit,
    ops::Deref,
    sync::{atomic::AtomicU8, Arc, Weak},
};

/// The state manager.
pub struct State {
    inner: UnsafeCell<MaybeUninit<Weak<StateRegistry>>>,
    initialized: AtomicU8,
}
impl State {
    const UNINITIALIZED: u8 = 0;
    const INITIALIZING: u8 = 1;
    const INITIALIZED: u8 = 2;

    /// Creates a new [`State`].
    ///
    /// # Example
    ///
    /// ```rust
    /// use state_department::State;
    ///
    /// static STATE: State = State::new();
    /// ```
    pub const fn new() -> Self {
        Self {
            inner: UnsafeCell::new(MaybeUninit::uninit()),
            initialized: AtomicU8::new(Self::UNINITIALIZED),
        }
    }

    /// Initializes the [`State`], giving you an entrypoint for populating
    /// the state with your desired values.
    ///
    /// # Panics
    ///
    /// * If the state has already been initialized.
    ///
    /// # Example
    ///
    /// ```rust
    /// use state_department::State;
    ///
    /// static STATE: State = State::new();
    ///
    /// struct Foo {
    ///     bar: i32
    /// }
    ///
    /// let _lifetime = STATE.init(|state| {
    ///     state.insert(Foo { bar: 42 });
    /// });
    ///
    /// assert_eq!(STATE.get::<Foo>().bar, 42);
    pub fn init<F>(&self, init: F) -> StateLifetime
    where
        F: FnOnce(&mut StateRegistry),
    {
        self.try_init(|inner| {
            init(inner);

            Ok::<_, ()>(())
        })
        .unwrap()
    }

    /// Initializes the [`State`], giving you a **fallible** entrypoint for
    /// populating the state with your desired values.
    ///
    /// # Panics
    ///
    /// * If the state has already been initialized.
    ///
    /// # Example
    ///
    /// ```rust
    /// use state_department::State;
    ///
    /// static STATE: State = State::new();
    ///
    /// let lifetime = STATE.try_init(|state| {
    ///     Err("oh no!")
    /// });
    ///
    /// assert!(lifetime.is_err());
    pub fn try_init<E, F>(&self, init: F) -> Result<StateLifetime, E>
    where
        F: FnOnce(&mut StateRegistry) -> Result<(), E>,
    {
        if self
            .initialized
            .compare_exchange(
                Self::UNINITIALIZED,
                Self::INITIALIZING,
                std::sync::atomic::Ordering::AcqRel,
                std::sync::atomic::Ordering::Acquire,
            )
            .is_err()
        {
            panic!("State already initialized or is currently initializing");
        }

        let mut result = Ok(());

        let inner = Arc::new_cyclic(|weak| {
            unsafe { (*self.inner.get()).write(weak.clone()) };

            let mut inner = StateRegistry::default();

            result = init(&mut inner);

            inner.map.shrink_to_fit();
            inner
        });

        result?;

        self.initialized
            .store(Self::INITIALIZED, std::sync::atomic::Ordering::Release);

        Ok(StateLifetime { inner: Some(inner) })
    }

    /// Returns a reference to a value stored in the state.
    ///
    /// # Panics
    ///
    /// * If the state has not yet been initialized.
    /// * If the state has been dropped.
    /// * If the state does not contain a value of the requested type.
    ///
    /// # Example
    ///
    /// ```rust
    /// use state_department::State;
    ///
    /// static STATE: State = State::new();
    ///
    /// struct Foo {
    ///     bar: i32
    /// }
    ///
    /// let _lifetime = STATE.init(|state| {
    ///     state.insert(Foo { bar: 42 });
    /// });
    ///
    /// let foo = STATE.get::<Foo>();
    ///
    /// assert_eq!(foo.bar, 42);
    /// ```
    #[must_use]
    pub fn get<T: Sync + 'static>(&self) -> StateRef<'_, T> {
        match self.initialized.load(std::sync::atomic::Ordering::Acquire) {
            Self::INITIALIZED => {}
            Self::INITIALIZING => panic!("State not yet initialized"),
            Self::UNINITIALIZED => panic!("State not yet initialized"),
            _ => unreachable!(),
        }

        let inner = match unsafe { (*self.inner.get()).assume_init_ref() }.upgrade() {
            Some(inner) => inner,
            None => panic!("State dropped"),
        };

        let v: &T = match inner
            .map
            .get(&TypeId::of::<T>())
            .and_then(|v| v.downcast_ref())
        {
            Some(v) => v,
            None => panic!("State for {:?} not found", std::any::type_name::<T>()),
        };

        StateRef {
            ptr: v,
            _life: inner,
            _phantom: PhantomData,
        }
    }

    /// Attempts to get a reference to a value stored in the state.
    ///
    /// This function does not panic.
    ///
    /// # Example
    ///
    /// ```rust
    /// use state_department::State;
    ///
    /// static STATE: State = State::new();
    ///
    /// struct Foo {
    ///     bar: i32
    /// }
    ///
    /// let _lifetime = STATE.init(|state| {
    ///     state.insert(Foo { bar: 42 });
    /// });
    ///
    /// let foo = STATE.try_get::<Foo>();
    ///
    /// assert_eq!(foo.unwrap().bar, 42);
    ///
    /// let str = STATE.try_get::<String>();
    ///
    /// assert!(str.is_none());
    /// ```
    #[must_use]
    pub fn try_get<T: Sync + 'static>(&self) -> Option<StateRef<'_, T>> {
        if self.initialized.load(std::sync::atomic::Ordering::Acquire) != Self::INITIALIZED {
            return None;
        }

        let inner = unsafe { (*self.inner.get()).assume_init_ref() }.upgrade()?;

        let v: &T = inner
            .map
            .get(&TypeId::of::<T>())
            .and_then(|v| v.downcast_ref())?;

        Some(StateRef {
            ptr: v,
            _life: inner,
            _phantom: PhantomData,
        })
    }
}
impl Drop for State {
    fn drop(&mut self) {
        let initialized = self.initialized.get_mut();

        if matches!(*initialized, Self::INITIALIZED | Self::INITIALIZING) {
            *initialized = Self::INITIALIZING;

            unsafe { self.inner.get_mut().assume_init_drop() };
        }
    }
}
impl Default for State {
    fn default() -> Self {
        Self::new()
    }
}
unsafe impl Send for State {}
unsafe impl Sync for State {}

/// This is the lifetime of your state. If this value is dropped, your state
/// will be dropped with it, provided that there are no currently held
/// references to the state.
///
/// It's recommended that you gracefully drop the state yourself at the end
/// of your program by calling [`StateLifetime::try_drop`]. This gives you
/// an opportunity to raise an error, log a message, or otherwise handle the
/// situation where there are still held references to your state.
///
/// If this value is dropped and there are still held references to the state,
/// nothing will happen. The values held within the state will not be dropped
/// until the corresponding [`State`] is dropped.
#[must_use]
pub struct StateLifetime {
    inner: Option<Arc<StateRegistry>>,
}
impl StateLifetime {
    /// Attempts to drop the state, returning the [`StateLifetime`] as an
    /// [`Err`] if there are still held references.
    pub fn try_drop(mut self) -> Result<(), Self> {
        let Some(inner) = self.inner.take() else {
            return Err(self);
        };

        let Some(mut inner) = Arc::into_inner(inner) else {
            return Err(self);
        };

        inner.map.clear();

        Ok(())
    }
}
impl Drop for StateLifetime {
    fn drop(&mut self) {
        let Some(inner) = self.inner.take() else {
            return;
        };

        let Some(mut inner) = Arc::into_inner(inner) else {
            return;
        };

        inner.map.clear();
    }
}
impl std::fmt::Debug for StateLifetime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StateLifetime").finish()
    }
}

/// The registry of values stored in the [`State`].
///
/// You will be given an opportunity to populate this with your desired values
/// when initializing the [`State`] via [`State::init`] or [`State::try_init`].
#[derive(Default)]
pub struct StateRegistry {
    map: HashMap<TypeId, Box<dyn Any>>,
}
impl StateRegistry {
    /// Inserts a value into the state.
    pub fn insert<T: Sync + 'static>(&mut self, value: T) {
        self.map.insert(TypeId::of::<T>(), Box::new(value));
    }
}

/// A held reference to something in the [`State`].
///
/// Whilst this is held, [`StateLifetime::try_drop`] will return its [`Err`]
/// variant, and dropping the [`State`] will not drop the values held within it.
pub struct StateRef<'a, T> {
    _life: Arc<StateRegistry>,
    _phantom: std::marker::PhantomData<&'a ()>,
    ptr: *const T,
}
impl<T> Deref for StateRef<'_, T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.ptr }
    }
}

#[test]
fn test_state() {
    let state = State::new();

    struct Foo {
        bar: AtomicU8,
    }

    struct Baz {
        qux: i32,
    }

    let lifetime = state.init(|inner| {
        inner.insert(Foo {
            bar: AtomicU8::new(42),
        });

        inner.insert(Baz { qux: 24 });
    });

    {
        let foo = state.get::<Foo>();

        assert_eq!(foo.bar.load(std::sync::atomic::Ordering::Relaxed), 42);

        foo.bar.store(24, std::sync::atomic::Ordering::Release);
    }

    {
        let foo = state.get::<Foo>();

        assert_eq!(foo.bar.load(std::sync::atomic::Ordering::Acquire), 24);
    }

    {
        let baz = state.get::<Baz>();

        assert_eq!(baz.qux, 24);
    }

    lifetime.try_drop().unwrap();
}

#[test]
fn test_state_drop_with_ref() {
    let state = State::new();

    struct Foo;

    let lifetime = state.init(|inner| {
        inner.insert(Foo);
    });

    let _foo = state.get::<Foo>();

    let _ = lifetime.try_drop().unwrap_err();
}

#[test]
fn test_state_use_after_lifetime_drop() {
    let state = State::new();

    struct Foo;

    let lifetime = state.init(|inner| {
        inner.insert(Foo);
    });

    lifetime.try_drop().unwrap();

    assert!(state.try_get::<Foo>().is_none());
}

#[test]
fn test_state_drop_without_lifetime() {
    static DROPPED: AtomicU8 = AtomicU8::new(0);

    let state = State::new();

    struct Foo;
    impl Drop for Foo {
        fn drop(&mut self) {
            DROPPED.store(1, std::sync::atomic::Ordering::Release);
        }
    }

    let lifetime = state.init(|inner| {
        inner.insert(Foo);
    });

    let foo = state.get::<Foo>();

    assert_eq!(DROPPED.load(std::sync::atomic::Ordering::Acquire), 0);

    drop(lifetime);

    assert_eq!(DROPPED.load(std::sync::atomic::Ordering::Acquire), 0);

    drop(foo);

    assert_eq!(DROPPED.load(std::sync::atomic::Ordering::Acquire), 1);

    drop(state);

    assert_eq!(DROPPED.load(std::sync::atomic::Ordering::Acquire), 1);
}

#[test]
#[should_panic = "State already initialized or is currently initializing"]
fn test_state_already_initialized() {
    let state = State::new();
    let _ = state.init(|_| {});
    let _ = state.init(|_| {});
}

#[test]
fn test_state_across_threads() {
    static STATE: State = State::new();

    struct Foo {
        bar: AtomicU8,
    }

    let _lifetime = STATE.init(|state| {
        state.insert(Foo {
            bar: AtomicU8::new(0),
        });
    });

    let thread_count = 10;

    let barrier = std::sync::Arc::new(std::sync::Barrier::new(thread_count));

    let threads = (0..thread_count)
        .map(|_| {
            let barrier_ref = barrier.clone();

            std::thread::spawn(move || {
                barrier_ref.wait();

                STATE
                    .get::<Foo>()
                    .bar
                    .fetch_add(1, std::sync::atomic::Ordering::Release);
            })
        })
        .collect::<Vec<_>>();

    for thread in threads {
        thread.join().unwrap();
    }

    assert_eq!(
        STATE
            .get::<Foo>()
            .bar
            .load(std::sync::atomic::Ordering::Acquire),
        thread_count as u8
    );
}
