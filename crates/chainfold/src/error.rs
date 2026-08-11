use core::fmt;

use crate::{
    batch::BatchShapeError,
    position::{
        BlockRef,
        Position,
    },
};

/// Classified fold failure; the variant fixes the engine's recovery obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FoldError<E> {
    /// Event is not mine; engine counts it and advances the cursor.
    Skip(E),
    /// State is clean up to the previous position; recovery is rollback or resync.
    Halt(E),
    /// Apply mutated state partially; state is untrusted until a restore.
    Poison(E),
}

impl<E: fmt::Display> fmt::Display for FoldError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Skip(error) => write!(f, "skip: {error}"),
            Self::Halt(error) => write!(f, "halt: {error}"),
            Self::Poison(error) => write!(f, "poison: {error}"),
        }
    }
}

impl<E: fmt::Debug + fmt::Display> core::error::Error for FoldError<E> {}

/// Coarse-grained state of the fold engine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EngineStatus {
    /// Applying batches and advancing the cursor.
    Active,
    /// Fold refused an event with clean state below it.
    Halted {
        /// Position the fold halted at.
        at: Position,
    },
    /// Fold refused an event after mutating state.
    Poisoned {
        /// Position the fold poisoned at.
        at: Position,
    },
    /// Automated recovery is exhausted; only a reset leaves this state.
    Unrecoverable {
        /// Divergence that ended automated recovery.
        cause: DivergenceCause,
    },
}

impl EngineStatus {
    /// True while the engine still accepts batches.
    pub const fn is_active(&self) -> bool {
        matches!(self, Self::Active)
    }
}

impl fmt::Display for EngineStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Active => write!(f, "active"),
            Self::Halted { at } => {
                write!(f, "halted at block {} log index {}", at.block, at.log_index)
            }
            Self::Poisoned { at } => {
                write!(
                    f,
                    "poisoned at block {} log index {}",
                    at.block, at.log_index
                )
            }
            Self::Unrecoverable { cause } => write!(f, "unrecoverable: {cause}"),
        }
    }
}

impl core::error::Error for EngineStatus {}

/// Terminal divergence reason the engine cannot recover from automatically.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DivergenceCause {
    /// Fork deeper than the oldest observed block in the ring.
    ForkBeyondWindow,
    /// Replay is required but the source's horizon no longer covers the start block.
    HorizonExceeded {
        /// Block replay must start from.
        needed: u64,
        /// Oldest block the source still serves.
        horizon: u64,
    },
    /// Fold view disagreed with the anchor after retries.
    AnchorDivergence {
        /// Block whose anchor comparison failed.
        at: u64,
    },
}

impl fmt::Display for DivergenceCause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ForkBeyondWindow => write!(f, "fork deeper than the observed window"),
            Self::HorizonExceeded { needed, horizon } => {
                write!(
                    f,
                    "replay needs block {needed}, source horizon is {horizon}"
                )
            }
            Self::AnchorDivergence { at } => write!(f, "anchor divergence at block {at}"),
        }
    }
}

impl core::error::Error for DivergenceCause {}

/// Durability sink refused a snapshot offer; persistence has stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DurabilityLost;

impl fmt::Display for DurabilityLost {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "durability sink refused a snapshot; snapshots are no longer persisted"
        )
    }
}

impl core::error::Error for DurabilityLost {}

/// Rejected engine construction configuration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConfigError {
    /// Ring capacity is not a power of two.
    RingCapacityNotPowerOfTwo {
        /// Capacity the caller asked for.
        got: usize,
    },
    /// Ring capacity is outside the allowed range.
    RingCapacityOutOfRange {
        /// Capacity the caller asked for.
        got: usize,
    },
    /// Source cannot replay from the configured start block.
    HorizonExceedsStart {
        /// Block the driver folds from.
        start: u64,
        /// Oldest block the source still serves.
        horizon: u64,
    },
}

impl fmt::Display for ConfigError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RingCapacityNotPowerOfTwo { got } => {
                write!(f, "ring capacity {got} is not a power of two")
            }
            Self::RingCapacityOutOfRange { got } => {
                write!(f, "ring capacity {got} is out of the allowed range")
            }
            Self::HorizonExceedsStart { start, horizon } => {
                write!(f, "replay horizon {horizon} exceeds start block {start}")
            }
        }
    }
}

impl core::error::Error for ConfigError {}

/// Rejected or failed batch application.
#[derive(Debug, PartialEq, Eq)]
pub enum ApplyError<E> {
    /// Engine is halted, poisoned, or unrecoverable.
    NotActive {
        /// Status that refused the batch.
        status: EngineStatus,
    },
    /// Batch violates the flat layout rules.
    Shape(BatchShapeError),
    /// Cursor is set but the batch carries no boundary header.
    MissingBoundary,
    /// Boundary header names a block other than the cursor block.
    BoundaryNumberMismatch {
        /// Cursor block the boundary must name.
        expected: u64,
        /// Block the boundary named.
        got: u64,
    },
    /// Refetched header disagrees with the observed block of that number.
    ForkSuspected {
        /// Block as the engine observed it.
        observed: BlockRef,
        /// Block as the source refetched it.
        refetched: BlockRef,
    },
    /// Observed ring holds no entry for the cursor block, so no boundary is verifiable.
    CursorBlockUnobserved {
        /// Cursor block absent from the ring.
        block: u64,
    },
    /// Fold halted; state is clean up to the position before `at`.
    Halted {
        /// Position the fold refused.
        at: Position,
        /// Error the fold reported.
        error: E,
    },
    /// Fold poisoned; state is untrusted until a restore.
    Poisoned {
        /// Position the fold refused after mutating.
        at: Position,
        /// Error the fold reported.
        error: E,
    },
}

impl<E: fmt::Display> fmt::Display for ApplyError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotActive { status } => write!(f, "engine not active: {status}"),
            Self::Shape(error) => write!(f, "batch shape invalid: {error}"),
            Self::MissingBoundary => {
                write!(f, "cursor is set but the batch carries no boundary")
            }
            Self::BoundaryNumberMismatch { expected, got } => {
                write!(
                    f,
                    "boundary block {got} does not match cursor block {expected}"
                )
            }
            Self::ForkSuspected {
                observed,
                refetched,
            } => {
                write!(
                    f,
                    "fork suspected at block {}: observed hash {}, refetched hash {}",
                    observed.number,
                    HexHash(&observed.hash),
                    HexHash(&refetched.hash)
                )
            }
            Self::CursorBlockUnobserved { block } => {
                write!(f, "observed ring holds no entry for cursor block {block}")
            }
            Self::Halted { at, error } => {
                write!(
                    f,
                    "halted at block {} log index {}: {error}",
                    at.block, at.log_index
                )
            }
            Self::Poisoned { at, error } => {
                write!(
                    f,
                    "poisoned at block {} log index {}: {error}",
                    at.block, at.log_index
                )
            }
        }
    }
}

impl<E: fmt::Debug + fmt::Display> core::error::Error for ApplyError<E> {}

/// Rejected rollback request.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RollbackError {
    /// No retained checkpoint sits at or below the requested block.
    NoCheckpointAtOrBelow {
        /// Block the rollback targeted.
        block: u64,
    },
    /// Engine is unrecoverable; only a reset leaves this state.
    Unrecoverable {
        /// Divergence that ended automated recovery.
        cause: DivergenceCause,
    },
}

impl fmt::Display for RollbackError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoCheckpointAtOrBelow { block } => {
                write!(f, "no retained checkpoint at or below block {block}")
            }
            Self::Unrecoverable { cause } => write!(f, "unrecoverable: {cause}"),
        }
    }
}

impl core::error::Error for RollbackError {}

/// Renders a 32-byte hash as lowercase hex.
struct HexHash<'a>(&'a [u8; 32]);

impl fmt::Display for HexHash<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
            write!(f, "{byte:02x}")?;
        }
        Ok(())
    }
}
