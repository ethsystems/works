#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use crate::{
    position::{
        Position,
        pos_gt,
    },
    ring::BlockRing,
};
#[cfg(verus_keep_ghost)]
use {
    crate::verus::model::{
        SlotView,
        fview,
    },
    vstd::prelude::*,
};

/// Fixed K-slot ring of engine restore points.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug)]
pub(crate) struct CheckpointRing<F> {
    slots: Vec<Option<Slot<F>>>,
    next: usize,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug)]
pub(crate) struct Slot<F> {
    pub(crate) fold: F,
    pub(crate) cursor: Option<Position>,
}

/// True when the engine's ring can still serve the slot's window.
fn live<F>(slot: &Slot<F>, ring: &BlockRing) -> bool {
    match slot.cursor {
        Some(cursor) => ring.observes(cursor.block),
        None => true,
    }
}

impl<F> CheckpointRing<F> {
    pub(crate) fn new(slots: usize) -> Self {
        Self {
            slots: (0..slots).map(|_| None).collect(),
            next: 0,
        }
    }

    /// The `k`th stored slot oldest first, if it is live; the next write position holds
    /// the oldest. `k` must be below the slot count.
    fn live_at<'a>(&'a self, k: usize, ring: &BlockRing) -> Option<&'a Slot<F>> {
        let (newest, oldest) = self.slots.split_at(self.next);
        let entry = if k < oldest.len() {
            &oldest[k]
        } else {
            &newest[k - oldest.len()]
        };
        match entry {
            Some(slot) if live(slot, ring) => Some(slot),
            _ => None,
        }
    }

    pub(crate) fn count(&self, ring: &BlockRing) -> usize {
        let mut live = 0;
        for k in 0..self.slots.len() {
            if self.live_at(k, ring).is_some() {
                live += 1;
            }
        }
        live
    }

    /// Stores a slot at the next write position; overwrites the oldest when full.
    pub(crate) fn store(&mut self, slot: Slot<F>) {
        let len = self.slots.len();
        if len == 0 {
            return;
        }
        self.slots[self.next] = Some(slot);
        self.next = (self.next + 1) % len;
    }

    /// Oldest live slot; the mirror of best_at_or_below's newest-first scan.
    pub(crate) fn oldest<'a>(&'a self, ring: &BlockRing) -> Option<&'a Slot<F>> {
        for k in 0..self.slots.len() {
            if let Some(slot) = self.live_at(k, ring) {
                return Some(slot);
            }
        }
        None
    }

    /// Newest live slot with cursor block at or below the argument; empty-cursor slots
    /// always qualify.
    #[cold]
    pub(crate) fn best_at_or_below<'a>(
        &'a self,
        block: u64,
        ring: &BlockRing,
    ) -> Option<&'a Slot<F>> {
        let mut k = self.slots.len();
        while k > 0 {
            k -= 1;
            if let Some(slot) = self.live_at(k, ring) {
                let qualifies = match slot.cursor {
                    Some(cursor) => cursor.block <= block,
                    None => true,
                };
                if qualifies {
                    return Some(slot);
                }
            }
        }
        None
    }

    /// Drops every slot whose cursor is after the argument, expired slots included, so
    /// none can come back to life when a later refold re-enters its block.
    #[cold]
    pub(crate) fn drop_newer(&mut self, cursor: Option<Position>) {
        for i in 0..self.slots.len() {
            let newer = match &self.slots[i] {
                Some(slot) => pos_gt(slot.cursor, cursor),
                None => false,
            };
            if newer {
                self.slots[i] = None;
            }
        }
    }

    pub(crate) fn clear(&mut self) {
        for i in 0..self.slots.len() {
            self.slots[i] = None;
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl<F> View for Slot<F> {
    type V = SlotView;

    closed spec fn view(&self) -> SlotView {
        SlotView { fold: fview::<F>(&self.fold), cursor: self.cursor }
    }
}

impl<F> CheckpointRing<F> {
    /// The write position is a slot, or 0 with no slots (K = 0).
    pub(crate) closed spec fn wf(&self) -> bool {
        self.next < self.slots@.len() || (self.next == 0 && self.slots@.len() == 0)
    }
}

impl<F> View for CheckpointRing<F> {
    /// One entry per slot, oldest stored first: logical `k` is physical `(next + k) % K`.
    type V = Seq<Option<SlotView>>;

    closed spec fn view(&self) -> Seq<Option<SlotView>> {
        let k = self.slots@.len() as int;
        Seq::new(
            k as nat,
            |i: int|
                match self.slots@[(self.next + i) % k] {
                    Some(slot) => Some(slot@),
                    None => None,
                },
        )
    }
}
} // verus!
