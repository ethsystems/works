#![cfg_attr(feature = "docs", doc = include_utils::include_md!("README.md:intro"))]
#![cfg_attr(feature = "docs", doc = include_utils::include_md!("README.md:design"))]
#![cfg_attr(feature = "docs", doc = include_utils::include_md!("README.md:usage"))]
#![cfg_attr(not(test), deny(clippy::cast_possible_truncation))]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![deny(unused_crate_dependencies)]
#![deny(warnings)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
#[cfg_attr(docsrs, doc(cfg(not(feature = "std"))))]
extern crate alloc;

// dev-only crates linked into the test harness build.
#[cfg(test)]
use {
    chainfold as _,
    criterion as _,
    proptest as _,
    tempfile as _,
    tokio as _,
};

// The checksum takes crc-fast on std and crc otherwise; std links the idle one unused.
#[cfg(all(feature = "std", feature = "wincode"))]
use crc as _;
#[cfg(all(feature = "std", not(feature = "wincode")))]
use crc_fast as _;

mod anchor;
mod batch;
mod checkpoint;
mod driver;
mod engine;
mod error;
mod fold;
mod position;
mod ring;
mod sink;
mod source;

#[cfg(feature = "wincode")]
mod snapshot;

#[cfg(feature = "tokio")]
#[cfg_attr(docsrs, doc(cfg(feature = "tokio")))]
pub mod harness;

#[cfg(feature = "storage")]
#[cfg_attr(docsrs, doc(cfg(feature = "storage")))]
pub mod storage;

#[cfg(any(test, feature = "test-helpers"))]
#[cfg_attr(docsrs, doc(cfg(feature = "test-helpers")))]
pub mod test_util;

pub use anchor::{
    Anchor,
    NoAnchor,
};
pub use batch::{
    Batch,
    BatchShapeError,
    SpanView,
    Spans,
};
pub use driver::{
    Driver,
    DriverConfig,
    DriverStatus,
    Probed,
    Tick,
    Tickable,
};
pub use engine::{
    ApplySummary,
    Engine,
    EngineConfig,
};
pub use error::{
    ApplyError,
    ConfigError,
    DivergenceCause,
    DurabilityLost,
    EngineStatus,
    FoldError,
    RollbackError,
};
pub use fold::Fold;
pub use position::{
    BlockRef,
    Position,
};
pub use ring::Observed;
pub use sink::{
    NoSink,
    SnapshotSink,
};
pub use source::{
    EventSource,
    ProbeSource,
    ReplayHorizon,
};

#[cfg(feature = "wincode")]
#[cfg_attr(docsrs, doc(cfg(feature = "wincode")))]
pub use snapshot::{
    Persist,
    SNAPSHOT_MAGIC,
    SNAPSHOT_VERSION,
    SnapshotError,
};
