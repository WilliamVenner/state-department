#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![cfg_attr(docsrs, feature(doc_cfg))]

const UNINITIALIZED: u8 = 0;
const INITIALIZING: u8 = 1;
const INITIALIZED: u8 = 2;

#[cfg_attr(docsrs, doc(cfg(feature = "async")))]
#[cfg(feature = "async")]
mod r#async;
mod lazy;
mod manager;
mod state;

pub use manager::*;
pub use state::AnyContext;

/// State manager for any (synchronous or asynchronous) contexts.
pub type State = manager::StateManager<AnyContext>;

/// State manager for asynchronous-only contexts.
///
/// This state manager is an extension of [`State`] but allows you to register
/// and get `async` lazy initialized global state (see
/// [`StateRegistry::insert_async_lazy`])
#[cfg(feature = "async")]
#[cfg_attr(docsrs, doc(cfg(feature = "async")))]
pub type AsyncState = manager::StateManager<AsyncOnlyContext>;

#[cfg(feature = "async")]
#[cfg_attr(docsrs, doc(cfg(feature = "async")))]
pub use r#async::AsyncOnlyContext;
