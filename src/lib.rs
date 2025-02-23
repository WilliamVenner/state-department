#![doc = include_str!("../README.md")]
#![deny(missing_docs)]

use std::{
    any::{Any, TypeId},
    cell::UnsafeCell,
    collections::HashMap,
    marker::PhantomData,
    mem::MaybeUninit,
    ops::Deref,
    sync::{atomic::AtomicU8, Arc, LazyLock, Weak},
};

/// The state manager.
pub struct State {
    state: UnsafeCell<MaybeUninit<Weak<StateRegistry>>>,
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
            state: UnsafeCell::new(MaybeUninit::uninit()),
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
    /// ```
    pub fn init<F>(&self, init: F) -> StateLifetime
    where
        F: FnOnce(&mut StateRegistry),
    {
        self.try_init(|state| {
            init(state);

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
    /// ```
    pub fn try_init<E, F>(&self, init: F) -> Result<StateLifetime, E>
    where
        F: FnOnce(&mut StateRegistry) -> Result<(), E>,
    {
        self.start_init();

        let mut state = StateRegistry::default();

        init(&mut state)?;

        Ok(self.finish_init(state))
    }

    /// Initializes the [`State`] asynchronously, giving you an entrypoint for
    /// populating the state with your desired values in an asynchronous
    /// context.
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
    /// # tokio_test::block_on(async {
    /// let _lifetime = STATE.init_async(async |state| {
    ///     state.insert(Foo { bar: 42 });
    /// })
    /// .await;
    ///
    /// assert_eq!(STATE.get::<Foo>().bar, 42);
    /// # });
    /// ```
    pub async fn init_async<F>(&self, init: F) -> StateLifetime
    where
        F: AsyncFnOnce(&mut StateRegistry),
    {
        self.try_init_async(async |state: &mut StateRegistry| {
            init(state).await;

            Ok::<_, ()>(())
        })
        .await
        .unwrap()
    }

    /// Initializes the [`State`] asynchronously, giving you a **fallible**
    /// entrypoint for populating the state with your desired values in an
    /// asynchronous context.
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
    /// # tokio_test::block_on(async {
    /// let lifetime = STATE.try_init_async(async |state| {
    /// #   state.insert(());
    ///
    ///     Err("oh no!")
    /// });
    ///
    /// assert!(lifetime.await.is_err());
    /// # });
    /// ```
    pub async fn try_init_async<E, F>(&self, init: F) -> Result<StateLifetime, E>
    where
        F: AsyncFnOnce(&mut StateRegistry) -> Result<(), E>,
    {
        self.start_init();

        let mut state = StateRegistry::default();

        init(&mut state).await?;

        Ok(self.finish_init(state))
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
    pub fn get<T: Send + Sync + 'static>(&self) -> StateRef<'_, T> {
        if self.initialized.load(std::sync::atomic::Ordering::Acquire) != Self::INITIALIZED {
            panic!("State not yet initialized");
        }

        let state = match unsafe { (*self.state.get()).assume_init_ref() }.upgrade() {
            Some(state) => state,
            None => panic!("State dropped"),
        };

        let v: &T = match state
            .map
            .get(&TypeId::of::<T>())
            .and_then(|v| LazyState::downcast_ref_lazy(v))
        {
            Some(v) => v,
            None => panic!("State for {:?} not found", std::any::type_name::<T>()),
        };

        StateRef {
            value: v,
            _state: state,
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
    pub fn try_get<T: Send + Sync + 'static>(&self) -> Option<StateRef<'_, T>> {
        if self.initialized.load(std::sync::atomic::Ordering::Acquire) != Self::INITIALIZED {
            return None;
        }

        let state = unsafe { (*self.state.get()).assume_init_ref() }.upgrade()?;

        let value: &T = state
            .map
            .get(&TypeId::of::<T>())
            .and_then(|v| LazyState::downcast_ref_lazy(v))?;

        Some(StateRef {
            value,
            _state: state,
            _phantom: PhantomData,
        })
    }

    fn start_init(&self) {
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
    }

    fn finish_init(&self, mut state: StateRegistry) -> StateLifetime {
        state.map.shrink_to_fit();

        // https://github.com/rust-lang/rust-clippy/issues/11382
        #[allow(clippy::arc_with_non_send_sync)]
        let state = Arc::new(state);

        unsafe { (*self.state.get()).write(Arc::downgrade(&state)) };

        self.initialized
            .store(Self::INITIALIZED, std::sync::atomic::Ordering::Release);

        StateLifetime { state: Some(state) }
    }
}
impl Drop for State {
    fn drop(&mut self) {
        let initialized = self.initialized.get_mut();

        if *initialized == Self::INITIALIZED {
            *initialized = Self::UNINITIALIZED;

            unsafe { self.state.get_mut().assume_init_drop() };
        }
    }
}
impl Default for State {
    fn default() -> Self {
        Self::new()
    }
}
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
    state: Option<Arc<StateRegistry>>,
}
impl StateLifetime {
    /// Attempts to drop the state, returning the [`StateLifetime`] as an
    /// [`Err`] if there are still held references.
    pub fn try_drop(mut self) -> Result<(), Self> {
        let Some(state) = self.state.take() else {
            return Err(self);
        };

        let Some(mut state) = Arc::into_inner(state) else {
            return Err(self);
        };

        state.map.clear();

        Ok(())
    }
}
impl Drop for StateLifetime {
    fn drop(&mut self) {
        let Some(state) = self.state.take() else {
            return;
        };

        let Some(mut state) = Arc::into_inner(state) else {
            return;
        };

        state.map.clear();
    }
}
impl std::fmt::Debug for StateLifetime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StateLifetime").finish()
    }
}

/// A held reference to something in the [`State`].
///
/// Whilst this is held, [`StateLifetime::try_drop`] will return its [`Err`]
/// variant, and dropping the [`State`] will not drop the values held within it.
pub struct StateRef<'a, T> {
    _state: Arc<StateRegistry>,
    _phantom: std::marker::PhantomData<&'a ()>,
    value: *const T,
}
impl<T> Deref for StateRef<'_, T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.value }
    }
}

/// The registry of values stored in the [`State`].
///
/// You will be given an opportunity to populate this with your desired values
/// when initializing the [`State`] via [`State::init`] or [`State::try_init`].
#[derive(Default)]
pub struct StateRegistry {
    map: HashMap<TypeId, Box<dyn Any + Send + Sync>>,
    _not_send: PhantomData<*mut ()>,
}
impl StateRegistry {
    /// Inserts a value into the state.
    pub fn insert<T: Send + Sync + 'static>(&mut self, value: T) {
        self.map.insert(TypeId::of::<T>(), Box::new(value));
    }

    /// Inserts a value into the state that is initialized lazily (when first
    /// accessed.)
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
    ///     state.insert_lazy(|| {
    ///         println!("Initializing Foo...");
    ///
    ///         // Something expensive or long-running...
    ///
    ///         Foo { bar: 42 }
    ///     });
    /// });
    ///
    /// let foo = STATE.get::<Foo>();
    ///
    /// // > Initializing Foo...
    /// ```
    pub fn insert_lazy<T: Send + Sync + 'static>(&mut self, init: fn() -> T) {
        self.map
            .insert(TypeId::of::<T>(), Box::new(LazyState(LazyLock::new(init))));
    }
}

struct LazyState<T: 'static>(LazyLock<T>);
impl<T> LazyState<T> {
    fn downcast_ref_lazy(v: &Box<dyn Any + Send + Sync>) -> Option<&T> {
        let v = v.as_ref() as &dyn Any;

        v.downcast_ref::<T>()
            .or_else(|| v.downcast_ref::<LazyState<T>>().map(|v| &*v.0))
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

    let lifetime = state.init(|state| {
        state.insert(Foo {
            bar: AtomicU8::new(42),
        });

        state.insert(Baz { qux: 24 });
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

    let lifetime = state.init(|state| {
        state.insert(Foo);
    });

    let _foo = state.get::<Foo>();

    let _ = lifetime.try_drop().unwrap_err();
}

#[test]
fn test_state_use_after_lifetime_drop() {
    let state = State::new();

    struct Foo;

    let lifetime = state.init(|state| {
        state.insert(Foo);
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

    let lifetime = state.init(|state| {
        state.insert(Foo);
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
fn test_lazy_initialization() {
    static FOO_INITIALIZED: AtomicU8 = AtomicU8::new(0);

    let state = State::new();

    struct Foo {
        bar: i32,
    }

    let _lifetime = state.init(|state| {
        state.insert_lazy(|| {
            FOO_INITIALIZED.store(1, std::sync::atomic::Ordering::Release);

            Foo { bar: 42 }
        });
    });

    assert_eq!(
        FOO_INITIALIZED.load(std::sync::atomic::Ordering::Acquire),
        0
    );

    let foo = state.get::<Foo>();

    assert_eq!(
        FOO_INITIALIZED.load(std::sync::atomic::Ordering::Acquire),
        1
    );

    assert_eq!(foo.bar, 42);
}

#[test]
#[should_panic = "State not yet initialized"]
fn test_state_get_inside_init() {
    let state = State::new();
    let _ = state.init(|_| {
        let _ = state.get::<()>();
    });
}

#[test]
#[should_panic = "State already initialized or is currently initializing"]
fn test_state_init_inside_init() {
    let state = State::new();
    let _ = state.init(|_| {
        let _ = state.init(|_| {});
    });
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
