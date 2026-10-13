//! Durable snapshot storage: filesystem abstraction, manifest codec, and the store.

mod flusher;
mod manifest;
mod store;
mod vfs;

pub use flusher::{
    FlushError,
    Flusher,
};
pub use store::{
    Recovered,
    SnapshotStore,
    StoreConfig,
    StoreError,
};
pub use vfs::{
    RealVfs,
    Vfs,
};
