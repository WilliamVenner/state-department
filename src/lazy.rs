use crate::StateRegistry;
use std::{any::TypeId, cell::UnsafeCell, sync::OnceLock};

impl<R> StateRegistry<R> {
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
    pub fn insert_lazy<T, F>(&mut self, init: F)
    where
        T: Send + Sync + 'static,
        F: FnOnce() -> T + Send + 'static,
    {
        self.map.insert(
            TypeId::of::<T>(),
            Box::new(LazyState {
                init: UnsafeCell::new(Some(Box::new(init))),
                once: OnceLock::new(),
            }),
        );
    }
}

pub(crate) struct LazyState<T: Send + Sync + 'static> {
    pub(crate) init: UnsafeCell<Option<Box<dyn FnOnce() -> T + Send>>>,
    pub(crate) once: OnceLock<T>,
}
impl<T: Send + Sync + 'static> LazyState<T> {
    pub(crate) fn get(&self) -> &T {
        self.once.get_or_init(|| {
            let init = unsafe { (*self.init.get()).take() }.unwrap();
            init()
        })
    }
}
unsafe impl<T: Send + Sync + 'static> Send for LazyState<T> {}
unsafe impl<T: Send + Sync + 'static> Sync for LazyState<T> {}
