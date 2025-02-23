use crate::{
    lazy::LazyState,
    manager::{StateManager, StateRef},
    INITIALIZED,
};
use std::{
    any::{Any, TypeId},
    marker::PhantomData,
};

/// A type bound for types that can be used in both synchronous and asynchronous
/// contexts.
pub struct AnyContext;

impl StateManager<AnyContext> {
    /// Creates a new [`StateManager`] appropriate for both synchronous and
    /// asynchronous contexts.
    ///
    /// # Example
    ///
    /// ```rust
    /// use state_department::State;
    ///
    /// static STATE: State = State::new();
    /// ```
    pub const fn new() -> Self {
        Self::new_()
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
    pub fn get<T: Send + Sync + 'static>(&self) -> StateRef<'_, T, AnyContext> {
        match self.try_get() {
            Some(v) => v,
            None => panic!("State for {:?} not found", std::any::type_name::<T>()),
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
    pub fn try_get<T: Send + Sync + 'static>(&self) -> Option<StateRef<'_, T, AnyContext>> {
        if self.initialized.load(std::sync::atomic::Ordering::Acquire) != INITIALIZED {
            return None;
        }

        let state = unsafe { (*self.state.get()).assume_init_ref() }.upgrade()?;

        let value: &T = state.map.get(&TypeId::of::<T>()).and_then(|v| {
            let v = v.as_ref() as &dyn Any;

            v.downcast_ref::<T>()
                .or_else(|| v.downcast_ref::<LazyState<T>>().map(|v| v.get()))
        })?;

        Some(StateRef {
            value,
            _state: state,
            _phantom: PhantomData,
        })
    }
}
impl Default for StateManager<AnyContext> {
    fn default() -> Self {
        Self::new()
    }
}

#[test]
fn test_state() {
    use std::sync::atomic::AtomicU8;

    let state = StateManager::<AnyContext>::new();

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
    let state = StateManager::<AnyContext>::new();

    struct Foo;

    let lifetime = state.init(|state| {
        state.insert(Foo);
    });

    let _foo = state.get::<Foo>();

    let _ = lifetime.try_drop().unwrap_err();
}

#[test]
fn test_state_use_after_lifetime_drop() {
    let state = StateManager::<AnyContext>::new();

    struct Foo;

    let lifetime = state.init(|state| {
        state.insert(Foo);
    });

    lifetime.try_drop().unwrap();

    assert!(state.try_get::<Foo>().is_none());
}

#[test]
fn test_state_drop_without_lifetime() {
    use std::sync::atomic::AtomicU8;

    static DROPPED: AtomicU8 = AtomicU8::new(0);

    let state = StateManager::<AnyContext>::new();

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
    use std::sync::atomic::AtomicU8;

    static FOO_INITIALIZED: AtomicU8 = AtomicU8::new(0);

    let state = StateManager::<AnyContext>::new();

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
fn test_state_across_threads() {
    use std::sync::atomic::AtomicU8;

    static STATE: StateManager<AnyContext> = StateManager::<AnyContext>::new();

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

#[test]
#[should_panic = "State for \"()\" not found"]
fn test_state_get_inside_init() {
    let state = StateManager::<AnyContext>::new();
    let _ = state.init(|r| {
        r.insert(());

        let _ = state.get::<()>();
    });
}

#[test]
#[should_panic = "State already initialized or is currently initializing"]
fn test_state_init_inside_init() {
    let state = StateManager::<AnyContext>::new();
    let _ = state.init(|_| {
        let _ = state.init(|_| {});
    });
}

#[test]
#[should_panic = "State already initialized or is currently initializing"]
fn test_state_already_initialized() {
    let state = StateManager::<AnyContext>::new();
    let _ = state.init(|_| {});
    let _ = state.init(|_| {});
}
