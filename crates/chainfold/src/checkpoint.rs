#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use crate::{
    position::Position,
    ring::BlockRing,
};

/// Fixed K-slot ring of engine restore points.
#[derive(Debug)]
pub(crate) struct CheckpointRing<F> {
    slots: Vec<Option<Slot<F>>>,
    next: usize,
}

#[derive(Debug)]
pub(crate) struct Slot<F> {
    pub(crate) fold: F,
    pub(crate) cursor: Option<Position>,
}

/// True when the engine's ring can still serve the slot's window.
fn live<F>(slot: &Slot<F>, ring: &BlockRing) -> bool {
    slot.cursor.is_none_or(|cursor| ring.observes(cursor.block))
}

impl<F> CheckpointRing<F> {
    pub(crate) fn new(slots: usize) -> Self {
        Self {
            slots: (0..slots).map(|_| None).collect(),
            next: 0,
        }
    }

    /// Live slots oldest first, since the next write position holds the oldest.
    fn oldest_first<'a>(
        &'a self,
        ring: &'a BlockRing,
    ) -> impl DoubleEndedIterator<Item = &'a Slot<F>> {
        let (newest, oldest) = self.slots.split_at(self.next);
        oldest
            .iter()
            .chain(newest)
            .flatten()
            .filter(move |slot| live(slot, ring))
    }

    pub(crate) fn count(&self, ring: &BlockRing) -> usize {
        self.oldest_first(ring).count()
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
    pub(crate) fn oldest<'a>(&'a self, ring: &'a BlockRing) -> Option<&'a Slot<F>> {
        self.oldest_first(ring).next()
    }

    /// Newest live slot with cursor block at or below the argument; empty-cursor slots
    /// always qualify.
    #[cold]
    pub(crate) fn best_at_or_below<'a>(
        &'a self,
        block: u64,
        ring: &'a BlockRing,
    ) -> Option<&'a Slot<F>> {
        self.oldest_first(ring)
            .rev()
            .find(|slot| slot.cursor.is_none_or(|cursor| cursor.block <= block))
    }

    /// Drops slots with cursor block strictly above the argument.
    #[cold]
    pub(crate) fn drop_above(&mut self, block: u64) {
        for slot in &mut self.slots {
            slot.take_if(|slot| slot.cursor.is_some_and(|cursor| cursor.block > block));
        }
    }

    pub(crate) fn clear(&mut self) {
        self.slots.fill_with(|| None);
    }
}
