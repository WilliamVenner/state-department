use crate::{
    lazy::LazyState,
    manager::{StateManager, StateRef},
    StateRegistry, INITIALIZED,
};
use async_once_cell::OnceCell;
use std::{
    any::{Any, TypeId},
    cell::UnsafeCell,
    future::Future,
    marker::PhantomData,
    pin::Pin,
};

/// A type bound for types that can be used in asynchronous-only contexts.
pub struct AsyncOnlyContext;

impl StateManager<AsyncOnlyContext> {
    /// Creates a new [`StateManager`] appropriate for asynchronous-only
    /// contexts.
    ///
    /// # Example
    ///
    /// ```rust
    /// use state_department::AsyncState;
    ///
    /// static STATE: AsyncState = AsyncState::new();
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
    /// use state_department::AsyncState;
    ///
    /// static STATE: AsyncState = AsyncState::new();
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
    /// let foo = STATE.get::<Foo>().await;
    ///
    /// assert_eq!(foo.bar, 42);
    /// # });
    /// ```
    #[must_use]
    pub async fn get<T: Send + Sync + 'static>(&self) -> StateRef<'_, T, AsyncOnlyContext> {
        match self.try_get().await {
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
    /// use state_department::AsyncState;
    ///
    /// static STATE: AsyncState = AsyncState::new();
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
    /// let foo = STATE.try_get::<Foo>().await;
    ///
    /// assert_eq!(foo.unwrap().bar, 42);
    ///
    /// let str = STATE.try_get::<String>().await;
    ///
    /// assert!(str.is_none());
    /// # });
    /// ```
    #[must_use]
    pub async fn try_get<T: Send + Sync + 'static>(
        &self,
    ) -> Option<StateRef<'_, T, AsyncOnlyContext>> {
        if self.initialized.load(std::sync::atomic::Ordering::Acquire) != INITIALIZED {
            return None;
        }

        let state = unsafe { (*self.state.get()).assume_init_ref() }.upgrade()?;

        if let Some(value) = state.get(&TypeId::of::<T>()) {
            let value = value.as_ref() as &dyn Any;

            if let Some(value) = value.downcast_ref::<T>() {
                return Some(StateRef {
                    value,
                    _state: state,
                    _phantom: PhantomData,
                });
            }

            if let Some(value) = value.downcast_ref::<LazyState<T>>() {
                return Some(StateRef {
                    value: value.get(),
                    _state: state,
                    _phantom: PhantomData,
                });
            }

            if let Some(value) = value.downcast_ref::<AsyncLazyState<T>>() {
                return Some(StateRef {
                    value: value.get().await,
                    _state: state,
                    _phantom: PhantomData,
                });
            }
        }

        None
    }
}
impl Default for StateManager<AsyncOnlyContext> {
    fn default() -> Self {
        Self::new()
    }
}

impl StateRegistry<AsyncOnlyContext> {
    /// Inserts a value into the state that is initialized lazily (when first
    /// accessed) in an asynchronous context.
    ///
    /// # Example
    ///
    /// ```rust
    /// use state_department::AsyncState;
    ///
    /// static STATE: AsyncState = AsyncState::new();
    ///
    /// struct Foo {
    ///     bar: i32
    /// }
    ///
    /// # tokio_test::block_on(async {
    /// let _lifetime = STATE.init_async(async |state| {
    ///     state.insert_async_lazy(async {
    ///         println!("Initializing Foo...");
    ///
    ///         // Something expensive or long-running...
    ///
    ///         Foo { bar: 42 }
    ///     });
    /// })
    /// .await;
    ///
    /// let foo = STATE.get::<Foo>().await;
    /// # });
    ///
    /// // > Initializing Foo...
    /// ```
    pub fn insert_async_lazy<T, F>(&mut self, init: F)
    where
        T: Send + Sync + 'static,
        F: Future<Output = T> + Send + 'static,
    {
        self.insert_(
            TypeId::of::<T>(),
            Box::new(AsyncLazyState {
                init: UnsafeCell::new(Some(Box::pin(init))),
                once: OnceCell::new(),
            }),
        );
    }
}

struct AsyncLazyState<T: Send + Sync + 'static> {
    init: UnsafeCell<Option<Pin<Box<dyn Future<Output = T> + Send + 'static>>>>,
    once: OnceCell<T>,
}
impl<T: Send + Sync + 'static> AsyncLazyState<T> {
    async fn get(&self) -> &T {
        self.once
            .get_or_init(async {
                let init = unsafe { (*self.init.get()).take() }.unwrap();
                init.await
            })
            .await
    }
}
unsafe impl<T: Send + Sync + 'static> Send for AsyncLazyState<T> {}
unsafe impl<T: Send + Sync + 'static> Sync for AsyncLazyState<T> {}

#[test]
fn test_state() {
    use std::sync::atomic::AtomicU8;

    tokio_test::block_on(async {
        let state = StateManager::<AsyncOnlyContext>::new();

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
            let foo: StateRef<'_, Foo, AsyncOnlyContext> = state.get::<Foo>().await;

            assert_eq!(foo.bar.load(std::sync::atomic::Ordering::Relaxed), 42);

            foo.bar.store(24, std::sync::atomic::Ordering::Release);
        }

        {
            let foo = state.get::<Foo>().await;

            assert_eq!(foo.bar.load(std::sync::atomic::Ordering::Acquire), 24);
        }

        {
            let baz = state.get::<Baz>().await;

            assert_eq!(baz.qux, 24);
        }

        lifetime.try_drop().unwrap();
    });
}

#[test]
fn test_state_drop_with_ref() {
    tokio_test::block_on(async {
        let state = StateManager::<AsyncOnlyContext>::new();

        struct Foo;

        let lifetime = state.init(|state| {
            state.insert(Foo);
        });

        let _foo = state.get::<Foo>().await;

        let _ = lifetime.try_drop().unwrap_err();
    });
}

#[test]
fn test_state_use_after_lifetime_drop() {
    tokio_test::block_on(async {
        let state = StateManager::<AsyncOnlyContext>::new();

        struct Foo;

        let lifetime = state.init(|state| {
            state.insert(Foo);
        });

        lifetime.try_drop().unwrap();

        assert!(state.try_get::<Foo>().await.is_none());
    });
}

#[test]
fn test_state_drop_without_lifetime() {
    use std::sync::atomic::AtomicU8;

    static DROPPED: AtomicU8 = AtomicU8::new(0);

    tokio_test::block_on(async {
        let state = StateManager::<AsyncOnlyContext>::new();

        struct Foo;
        impl Drop for Foo {
            fn drop(&mut self) {
                DROPPED.store(1, std::sync::atomic::Ordering::Release);
            }
        }

        let lifetime = state.init(|state| {
            state.insert(Foo);
        });

        let foo = state.get::<Foo>().await;

        assert_eq!(DROPPED.load(std::sync::atomic::Ordering::Acquire), 0);

        drop(lifetime);

        assert_eq!(DROPPED.load(std::sync::atomic::Ordering::Acquire), 0);

        drop(foo);

        assert_eq!(DROPPED.load(std::sync::atomic::Ordering::Acquire), 1);

        drop(state);

        assert_eq!(DROPPED.load(std::sync::atomic::Ordering::Acquire), 1);
    });
}

#[test]
fn test_lazy_initialization() {
    use std::sync::atomic::AtomicU8;

    static FOO_INITIALIZED: AtomicU8 = AtomicU8::new(0);

    tokio_test::block_on(async {
        let state = StateManager::<AsyncOnlyContext>::new();

        struct Foo {
            bar: i32,
        }

        let _lifetime = state.init(|state| {
            state.insert_async_lazy(async {
                FOO_INITIALIZED.store(1, std::sync::atomic::Ordering::Release);

                Foo { bar: 42 }
            });
        });

        assert_eq!(
            FOO_INITIALIZED.load(std::sync::atomic::Ordering::Acquire),
            0
        );

        let foo = state.get::<Foo>().await;

        assert_eq!(
            FOO_INITIALIZED.load(std::sync::atomic::Ordering::Acquire),
            1
        );

        assert_eq!(foo.bar, 42);
    });
}

#[test]
fn test_sync_lazy_initialization_from_async() {
    use std::sync::atomic::AtomicU8;

    static FOO_INITIALIZED: AtomicU8 = AtomicU8::new(0);

    tokio_test::block_on(async {
        let state = StateManager::<AsyncOnlyContext>::new();

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

        let foo = state.get::<Foo>().await;

        assert_eq!(
            FOO_INITIALIZED.load(std::sync::atomic::Ordering::Acquire),
            1
        );

        assert_eq!(foo.bar, 42);
    });
}

#[test]
fn test_state_across_threads() {
    use std::sync::atomic::AtomicU8;

    static STATE: StateManager<AsyncOnlyContext> = StateManager::<AsyncOnlyContext>::new();

    tokio_test::block_on(async {
        struct Foo {
            bar: AtomicU8,
        }

        let _lifetime = STATE.init(|state| {
            state.insert(Foo {
                bar: AtomicU8::new(0),
            });
        });

        let thread_count = 10;

        let barrier = std::sync::Arc::new(tokio::sync::Barrier::new(thread_count));

        let threads = (0..thread_count)
            .map(|_| {
                let barrier_ref = barrier.clone();

                tokio::spawn(async move {
                    barrier_ref.wait().await;

                    STATE
                        .get::<Foo>()
                        .await
                        .bar
                        .fetch_add(1, std::sync::atomic::Ordering::Release);
                })
            })
            .collect::<Vec<_>>();

        for thread in threads {
            thread.await.unwrap();
        }

        assert_eq!(
            STATE
                .get::<Foo>()
                .await
                .bar
                .load(std::sync::atomic::Ordering::Acquire),
            thread_count as u8
        );
    });
}

#[test]
#[should_panic = "State for \"()\" not found"]
fn test_state_get_inside_init() {
    tokio_test::block_on(async {
        let state = StateManager::<AsyncOnlyContext>::new();
        let _ = state
            .init_async(async |r| {
                r.insert(());

                let _ = state.get::<()>().await;
            })
            .await;
    });
}

#[test]
#[should_panic = "State already initialized or is currently initializing"]
fn test_state_init_inside_init() {
    tokio_test::block_on(async {
        let state = StateManager::<AsyncOnlyContext>::new();
        let _ = state.init(|_| {
            let _ = state.init(|_| {});
        });
    });
}

#[test]
#[should_panic = "State already initialized or is currently initializing"]
fn test_state_already_initialized() {
    tokio_test::block_on(async {
        let state = StateManager::<AsyncOnlyContext>::new();
        let _ = state.init(|_| {});
        let _ = state.init(|_| {});
    });
}
