#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use crate::position::BlockRef;
#[cfg(verus_keep_ghost)]
use {
    crate::verus::model::{
        a1,
        header,
        range_entries,
        sview,
        sview_log,
    },
    vstd::prelude::*,
};

/// Blocks per range query. 500 clears the common `eth_getLogs` limits.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const DEFAULT_WINDOW: u64 = 500;

/// Oldest position a source can replay from.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReplayHorizon {
    /// Source replays the whole chain.
    Genesis,
    /// Source replays only from this block upward.
    FromBlock(u64),
}

/// Random-access event supply over one chain.
// Each call answers from one view, `sview` of the source after the call, and every view
// satisfies `a1`. `sview_log` records those views in call order. Implementations are
// trusted to meet this spec.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait Source {
    /// Consumer event the source decodes its wire format into.
    type Event;
    /// Failure reading the source.
    type Error;

    /// Highest block this source will serve.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            a1::<Self, Self::Event>(sview::<Self>(final(self))),
            sview_log::<Self>(final(self)) == sview_log::<Self>(old(self)).push(
                sview::<Self>(final(self)),
            ),
    ))]
    fn head(&mut self) -> Result<u64, Self::Error>;

    /// Header of one block, or None when it is not on the current chain.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            a1::<Self, Self::Event>(sview::<Self>(final(self))),
            sview_log::<Self>(final(self)) == sview_log::<Self>(old(self)).push(
                sview::<Self>(final(self)),
            ),
            r matches Ok(h) ==> h == header(sview::<Self>(final(self)), number),
    ))]
    fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, Self::Error>;

    /// Appends every event in `from..=to`. Any order; the driver sorts and groups.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            a1::<Self, Self::Event>(sview::<Self>(final(self))),
            sview_log::<Self>(final(self)) == sview_log::<Self>(old(self)).push(
                sview::<Self>(final(self)),
            ),
            r is Ok ==> {
                let (pre, post) = (old(out)@, final(out)@);
                &&& pre.len() <= post.len()
                &&& post.subrange(0, pre.len() as int) == pre
                &&& post.subrange(pre.len() as int, post.len() as int).to_multiset()
                    == range_entries::<Self, Self::Event>(
                        sview::<Self>(final(self)),
                        from as int,
                        to as int,
                    ).to_multiset()
            },
    ))]
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
