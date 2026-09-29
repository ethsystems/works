#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use crate::position::BlockRef;
#[cfg(verus_keep_ghost)]
use {
    crate::verus::model::{
        a1,
        anc,
        hash_entries,
        header,
        infallible,
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

/// The head block and its parent's hash, from one header read.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Head {
    /// The head block.
    pub block: BlockRef,
    /// Hash of the head block's parent.
    pub parent: [u8; 32],
}

/// Random-access event supply over one chain.
// Each call answers from one view, `sview` of the source after the call, and every view
// satisfies `a1`. `sview_log` records those views in call order. A source in an
// `infallible` state answers every call and stays in one. Implementations are trusted to
// meet this spec.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait Source {
    /// Consumer event the source decodes its wire format into.
    type Event;
    /// Failure reading the source.
    type Error;

    /// Highest block this source will serve, with its parent's hash.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            a1::<Self, Self::Event>(sview::<Self>(final(self))),
            sview_log::<Self>(final(self)) == sview_log::<Self>(old(self)).push(
                sview::<Self>(final(self)),
            ),
            infallible::<Self>(old(self)) ==> r is Ok && infallible::<Self>(final(self)),
            r matches Ok(h) ==> header(sview::<Self>(final(self)), h.block.number) == Some(h.block)
                && (h.block.number > 0 ==> anc(h.block.hash, (h.block.number - 1) as u64).hash == h.parent),
    ))]
    fn head(&mut self) -> Result<Head, Self::Error>;

    /// Header of one block, or None when it is not on the current chain.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            a1::<Self, Self::Event>(sview::<Self>(final(self))),
            sview_log::<Self>(final(self)) == sview_log::<Self>(old(self)).push(
                sview::<Self>(final(self)),
            ),
            infallible::<Self>(old(self)) ==> r is Ok && infallible::<Self>(final(self)),
            r matches Ok(h) ==> h == header(sview::<Self>(final(self)), number),
    ))]
    fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, Self::Error>;

    /// Appends every event in `from..=to`, exactly: no event of the range is left out and
    /// none is added. Any order; the driver sorts and groups. A range past the head of the
    /// node that answers it gives `Err`, not a short answer, unless every call answers from
    /// one chain: a short answer from a node that lags reads as blocks with no events.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            a1::<Self, Self::Event>(sview::<Self>(final(self))),
            sview_log::<Self>(final(self)) == sview_log::<Self>(old(self)).push(
                sview::<Self>(final(self)),
            ),
            infallible::<Self>(old(self)) ==> r is Ok && infallible::<Self>(final(self)),
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

    /// Appends every event of the block with hash `block.hash`, exactly: no log of that
    /// block is left out and none is added. Any order. A hash the source does not know, or
    /// whose block it has not executed, gives `Err`. A JSON-RPC source reads it with
    /// `eth_getLogs` by `blockHash`, never by number: a by-number read can answer another
    /// block at that height, or nothing from a node that lags.
    ///
    /// A source that holds the header for this hash, such as the one `head` just read, may
    /// answer from its `logsBloom` instead: `Ok` with nothing appended when the bloom rules
    /// out every address and topic of the source's filter. That is exact, since the hash
    /// commits to the header and a bloom has no false negatives. The bloom test must set
    /// the bits as the chain does (three 11-bit indices from the keccak-256 of each address
    /// and topic) and read the filter as the node does (any of its addresses, and at each
    /// topic position it names, any of the topics listed there). A wrong test skips events
    /// and nothing reports it.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            a1::<Self, Self::Event>(sview::<Self>(final(self))),
            sview_log::<Self>(final(self)) == sview_log::<Self>(old(self)).push(
                sview::<Self>(final(self)),
            ),
            infallible::<Self>(old(self)) ==> r is Ok && infallible::<Self>(final(self)),
            r is Ok ==> {
                let (pre, post) = (old(out)@, final(out)@);
                &&& pre.len() <= post.len()
                &&& post.subrange(0, pre.len() as int) == pre
                &&& post.subrange(pre.len() as int, post.len() as int).to_multiset()
                    == hash_entries::<Self, Self::Event>(*block).to_multiset()
            },
    ))]
    fn events_at(
        &mut self,
        block: &BlockRef,
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
