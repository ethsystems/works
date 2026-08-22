#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use crate::position::BlockRef;

/// Blocks per range query. 500 clears the common `eth_getLogs` limits.
pub const DEFAULT_WINDOW: u64 = 500;

/// Oldest position a source can replay from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReplayHorizon {
    /// Source replays the whole chain.
    Genesis,
    /// Source replays only from this block upward.
    FromBlock(u64),
}

/// Random-access event supply over one chain.
pub trait Source {
    /// Consumer event the source decodes its wire format into.
    type Event;
    /// Failure reading the source.
    type Error;

    /// Highest block this source will serve.
    fn head(&mut self) -> Result<u64, Self::Error>;

    /// Header of one block, or None when it is not on the current chain.
    fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, Self::Error>;

    /// Appends every event in `from..=to`. Any order; the driver sorts and groups.
    fn events_in(
        &mut self,
        from: u64,
        to: u64,
        out: &mut Vec<(BlockRef, u32, Self::Event)>,
    ) -> Result<(), Self::Error>;

    /// Oldest block this source can still replay.
    fn horizon(&self) -> ReplayHorizon {
        ReplayHorizon::Genesis
    }

    /// Blocks per `events_in` call. Nodes cap the span.
    fn window(&self) -> u64 {
        DEFAULT_WINDOW
    }
}
