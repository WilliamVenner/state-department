use crate::{INITIALIZED, INITIALIZING, UNINITIALIZED};
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
pub struct StateManager<R> {
    pub(crate) state: UnsafeCell<MaybeUninit<Weak<StateRegistry<R>>>>,
    pub(crate) initialized: AtomicU8,
    pub(crate) _phantom: PhantomData<R>,
}
impl<R> StateManager<R> {
    pub(crate) const fn new_() -> Self {
        Self {
            state: UnsafeCell::new(MaybeUninit::uninit()),
            initialized: AtomicU8::new(UNINITIALIZED),
            _phantom: PhantomData,
        }
    }

    /// Initializes the [`StateManager`], giving you an entrypoint for
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
    pub fn init<F>(&self, init: F) -> StateLifetime<R>
    where
        F: FnOnce(&mut StateRegistry<R>),
    {
        match self.try_init(|state| {
            init(state);

            Ok::<_, ()>(())
        }) {
            Some(Ok(result)) => result,
            Some(Err(_)) => unreachable!(),
            None => panic!("State already initialized or is currently initializing"),
        }
    }

    /// Initializes the [`StateManager`], giving you a **fallible** entrypoint
    /// for populating the state with your desired values.
    ///
    /// Returns `None` if the [`StateManager`] is already initialized.
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
    /// assert!(lifetime.unwrap().is_err());
    /// ```
    pub fn try_init<E, F>(&self, init: F) -> Option<Result<StateLifetime<R>, E>>
    where
        F: FnOnce(&mut StateRegistry<R>) -> Result<(), E>,
    {
        if !self.try_start_init() {
            return None;
        }

        let mut state = StateRegistry::default();

        let result = init(&mut state);
        let result = result.map(|_| self.finish_init(state));

        Some(result)
    }

    /// Initializes the [`StateManager`] asynchronously, giving you an
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
    pub async fn init_async<F>(&self, init: F) -> StateLifetime<R>
    where
        F: AsyncFnOnce(&mut StateRegistry<R>),
    {
        match self
            .try_init_async(async |state| {
                init(state).await;

                Ok::<_, ()>(())
            })
            .await
        {
            Some(Ok(result)) => result,
            Some(Err(_)) => unreachable!(),
            None => panic!("State already initialized or is currently initializing"),
        }
    }

    /// Initializes the [`StateManager`] asynchronously, giving you a
    /// **fallible** entrypoint for populating the state with your desired
    /// values in an asynchronous context.
    ///
    /// Returns `None` if the [`StateManager`] is already initialized.
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
    ///     Err("oh no!")
    /// });
    ///
    /// assert!(lifetime.await.unwrap().is_err());
    /// # });
    /// ```
    pub async fn try_init_async<E, F>(&self, init: F) -> Option<Result<StateLifetime<R>, E>>
    where
        F: AsyncFnOnce(&mut StateRegistry<R>) -> Result<(), E>,
    {
        if !self.try_start_init() {
            return None;
        }

        let mut state = StateRegistry::default();
        let result = init(&mut state).await;
        let result = result.map(|_| self.finish_init(state));

        Some(result)
    }

    #[must_use = "returns whether the state can now be initialized"]
    fn try_start_init(&self) -> bool {
        self.initialized
            .compare_exchange(
                UNINITIALIZED,
                INITIALIZING,
                std::sync::atomic::Ordering::AcqRel,
                std::sync::atomic::Ordering::Acquire,
            )
            .is_ok()
    }

    fn finish_init(&self, mut state: StateRegistry<R>) -> StateLifetime<R> {
        state.map.shrink_to_fit();

        // https://github.com/rust-lang/rust-clippy/issues/11382
        #[allow(clippy::arc_with_non_send_sync)]
        let state = Arc::new(state);

        unsafe { (*self.state.get()).write(Arc::downgrade(&state)) };

        self.initialized
            .store(INITIALIZED, std::sync::atomic::Ordering::Release);

        StateLifetime { state: Some(state) }
    }
}
impl<R> Drop for StateManager<R> {
    fn drop(&mut self) {
        let initialized = self.initialized.get_mut();

        if *initialized == INITIALIZED {
            *initialized = UNINITIALIZED;

            unsafe { self.state.get_mut().assume_init_drop() };
        }
    }
}
unsafe impl<R> Sync for StateManager<R> {}

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
/// until the corresponding [`StateManager`] is dropped.
#[must_use]
pub struct StateLifetime<R> {
    state: Option<Arc<StateRegistry<R>>>,
}
impl<R> StateLifetime<R> {
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
impl<R> Drop for StateLifetime<R> {
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
impl<R> std::fmt::Debug for StateLifetime<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StateLifetime").finish()
    }
}

/// A held reference to something in the [`StateManager`].
///
/// Whilst this is held, [`StateLifetime::try_drop`] will return its [`Err`]
/// variant, and dropping the [`StateManager`] will not drop the values held
/// within it.
pub struct StateRef<'a, T: Send + Sync + 'static, R> {
    pub(crate) _state: Arc<StateRegistry<R>>,
    pub(crate) _phantom: PhantomData<&'a ()>,
    pub(crate) value: *const T,
}
impl<T: Send + Sync + 'static, R> Deref for StateRef<'_, T, R> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.value }
    }
}
unsafe impl<T: Send + Sync + 'static, R> Send for StateRef<'_, T, R> {}
unsafe impl<T: Send + Sync + 'static, R> Sync for StateRef<'_, T, R> {}

/// The registry of values stored in the [`StateManager`].
///
/// You will be given an opportunity to populate this with your desired values
/// when initializing the [`StateManager`] via [`StateManager::init`] or
/// [`StateManager::try_init`].
pub struct StateRegistry<R> {
    pub(crate) map: HashMap<TypeId, Box<dyn Any + Send + Sync>>,
    _phantom: PhantomData<R>,
}
impl<R> Default for StateRegistry<R> {
    fn default() -> Self {
        Self {
            map: HashMap::new(),
            _phantom: PhantomData,
        }
    }
}
impl<R> StateRegistry<R> {
    /// Inserts a value into the state.
    pub fn insert<T: Send + Sync + 'static>(&mut self, value: T) {
        self.map.insert(TypeId::of::<T>(), Box::new(value));
    }
}
