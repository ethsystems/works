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
    crate::{
        position::BlockRef,
        verus::model::{
            SlotView,
            fview,
            live_count,
            opt_lt,
            qualifies,
        },
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
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        ring.wf(),
    ensures
        r == crate::verus::model::live(slot@, ring@),
))]
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
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
            ring.wf(),
            k < self@.len(),
        ensures
            match r {
                Some(slot) => self@[k as int] == Some(slot@) && crate::verus::model::live(
                    slot@,
                    ring@,
                ),
                None => !self.live_view(ring@, k as int),
            },
    ))]
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

    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
            ring.wf(),
        ensures
            r == live_count(self@, ring@, self@.len() as int),
    ))]
    pub(crate) fn count(&self, ring: &BlockRing) -> usize {
        let mut live = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.wf(),
                ring.wf(),
                self@.len() == self.slots@.len(),
                live == live_count(self@, ring@, k as int),
                live <= k,
        ))]
        for k in 0..self.slots.len() {
            if self.live_at(k, ring).is_some() {
                live += 1;
            }
        }
        live
    }

    /// Stores a slot at the next write position; overwrites the oldest when full.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@ == if old(self)@.len() == 0 {
                old(self)@
            } else {
                old(self)@.drop_first().push(
                    Some(SlotView { fold: fview::<F>(&slot.fold), cursor: slot.cursor }),
                )
            },
    ))]
    pub(crate) fn store(&mut self, slot: Slot<F>) {
        let len = self.slots.len();
        if len == 0 {
            return;
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost pre = self@;
            let ghost stored = slot@;
        }
        self.slots[self.next] = Some(slot);
        #[cfg(verus_keep_ghost)]
        proof! {
            if self.next + 1 < len {
                vstd::arithmetic::div_mod::lemma_small_mod((self.next + 1) as nat, len as nat);
            } else {
                vstd::arithmetic::div_mod::lemma_mod_self_0(len as int);
            }
        }
        self.next = (self.next + 1) % len;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(self@ =~= pre.drop_first().push(Some(stored)));
        }
    }

    /// Oldest live slot; the mirror of best_at_or_below's newest-first scan.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
            ring.wf(),
        ensures
            match r {
                Some(slot) => exists|k: int|
                    0 <= k < self@.len() && self@[k] == Some(slot@) && self.live_view(ring@, k)
                        && forall|j: int| 0 <= j < k ==> !#[trigger] self.live_view(ring@, j),
                None => forall|j: int| 0 <= j < self@.len() ==> !#[trigger] self.live_view(ring@, j),
            },
    ))]
    pub(crate) fn oldest<'a>(&'a self, ring: &BlockRing) -> Option<&'a Slot<F>> {
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.wf(),
                ring.wf(),
                self@.len() == self.slots@.len(),
                forall|j: int| 0 <= j < k ==> !#[trigger] self.live_view(ring@, j),
        ))]
        for k in 0..self.slots.len() {
            if let Some(slot) = self.live_at(k, ring) {
                return Some(slot);
            }
        }
        None
    }

    /// Newest live slot with cursor block at or below the argument; empty-cursor slots
    /// always qualify.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
            ring.wf(),
        ensures
            match r {
                Some(slot) => exists|k: int|
                    0 <= k < self@.len() && self@[k] == Some(slot@) && self.live_view(ring@, k)
                        && qualifies(slot@, block) && forall|j: int|
                        k < j < self@.len() ==> !(#[trigger] self.live_view(ring@, j) && qualifies(
                            self@[j].unwrap(),
                            block,
                        )),
                None => forall|j: int|
                    0 <= j < self@.len() ==> !(#[trigger] self.live_view(ring@, j) && qualifies(
                        self@[j].unwrap(),
                        block,
                    )),
            },
    ))]
    #[cold]
    pub(crate) fn best_at_or_below<'a>(
        &'a self,
        block: u64,
        ring: &BlockRing,
    ) -> Option<&'a Slot<F>> {
        let mut k = self.slots.len();
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.wf(),
                ring.wf(),
                self@.len() == self.slots@.len(),
                k <= self@.len(),
                forall|j: int|
                    k <= j < self@.len() ==> !(#[trigger] self.live_view(ring@, j) && qualifies(
                        self@[j].unwrap(),
                        block,
                    )),
            decreases k,
        ))]
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
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(!crate::verus::model::qualifies(self@[k as int].unwrap(), block));
                }
            }
        }
        None
    }

    /// Drops every slot whose cursor is after the argument, expired slots included, so
    /// none can come back to life when a later refold re-enters its block.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@.len() == old(self)@.len(),
            forall|k: int|
                0 <= k < old(self)@.len() ==> #[trigger] final(self)@[k] == if old(self)@[k] is Some
                    && opt_lt(cursor, old(self)@[k].unwrap().cursor) {
                    None
                } else {
                    old(self)@[k]
                },
    ))]
    #[cold]
    pub(crate) fn drop_newer(&mut self, cursor: Option<Position>) {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost pre = self.slots@;
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.next == old(self).next,
                self.slots@.len() == pre.len(),
                pre == old(self).slots@,
                forall|p: int|
                    0 <= p < pre.len() ==> #[trigger] self.slots@[p] == if p < i && Self::newer(
                        pre[p],
                        cursor,
                    ) {
                        None
                    } else {
                        pre[p]
                    },
        ))]
        for i in 0..self.slots.len() {
            let newer = match &self.slots[i] {
                Some(slot) => pos_gt(slot.cursor, cursor),
                None => false,
            };
            if newer {
                self.slots[i] = None;
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|k: int| 0 <= k < old(self)@.len() implies #[trigger] self@[k] == if old(
                self,
            )@[k] is Some && opt_lt(cursor, old(self)@[k].unwrap().cursor) {
                None
            } else {
                old(self)@[k]
            } by {
                let p = old(self).phys(k);
                assert(self@[k] == Self::slot_view(self.slots@[p]));
            }
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@.len() == old(self)@.len(),
            forall|k: int| 0 <= k < final(self)@.len() ==> #[trigger] final(self)@[k] is None,
    ))]
    pub(crate) fn clear(&mut self) {
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.next == old(self).next,
                self.slots@.len() == old(self).slots@.len(),
                forall|p: int| 0 <= p < i ==> #[trigger] self.slots@[p] is None,
        ))]
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

    /// Physical index of logical `i < K`: `(next + i) % K`, spelled without `%`.
    spec fn phys(&self, i: int) -> int {
        if self.next + i < self.slots@.len() {
            self.next + i
        } else {
            self.next + i - self.slots@.len()
        }
    }

    spec fn slot_view(s: Option<Slot<F>>) -> Option<SlotView> {
        match s {
            Some(slot) => Some(slot@),
            None => None,
        }
    }

    spec fn newer(s: Option<Slot<F>>, cursor: Option<Position>) -> bool {
        match s {
            Some(slot) => opt_lt(cursor, slot.cursor),
            None => false,
        }
    }

    /// Logical slot `k` is stored and live in `ring` (model `EngineView::live_at`).
    pub(crate) closed spec fn live_view(&self, ring: Seq<BlockRef>, k: int) -> bool {
        &&& 0 <= k < self@.len()
        &&& self@[k] is Some
        &&& crate::verus::model::live(self@[k].unwrap(), ring)
    }

    pub(crate) proof fn lemma_live_view(&self, ring: Seq<BlockRef>, k: int)
        ensures
            self.live_view(ring, k) == (0 <= k < self@.len() && self@[k] is Some
                && crate::verus::model::live(self@[k].unwrap(), ring)),
    {
    }
}

impl<F> View for CheckpointRing<F> {
    /// One entry per slot, oldest stored first: logical `k` is physical `(next + k) % K`.
    type V = Seq<Option<SlotView>>;

    closed spec fn view(&self) -> Seq<Option<SlotView>> {
        Seq::new(self.slots@.len(), |i: int| Self::slot_view(self.slots@[self.phys(i)]))
    }
}

impl<F> Slot<F> {
    /// The view's fields, for modules that cannot see its body.
    pub(crate) proof fn lemma_view(&self)
        ensures
            self@ == (SlotView { fold: fview::<F>(&self.fold), cursor: self.cursor }),
    {
    }
}
} // verus!
