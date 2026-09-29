#[cfg(not(feature = "std"))]
use alloc::{
    boxed::Box,
    vec,
};
#[cfg(feature = "std")]
use std::{
    boxed::Box,
    vec,
};

#[cfg(verus_keep_ghost)]
use {
    crate::verus::model::{
        ChainView,
        a1,
        confirmed_prefix,
        confirms,
        down_closed,
        observes,
        prefix_at_or_below,
        ring_chain,
        ring_push,
        sview,
        sview_log,
    },
    vstd::{
        arithmetic::{
            logarithm::{
                lemma_log_is_ordered,
                lemma_log_nonnegative,
                lemma_log_pow,
                log,
            },
            power2::{
                lemma_pow2,
                lemma_pow2_pos,
                lemma_pow2_unfold,
                lemma2_to64,
                pow2,
            },
        },
        prelude::*,
    },
};

use crate::{
    position::BlockRef,
    source::Source,
};

/// True when `n` is a power of two; spelled out rather than std's so the verifier can state it.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures
        r == (n != 0 && n & ((n - 1) as usize) == 0),
))]
pub(crate) const fn is_power_of_two(n: usize) -> bool {
    n != 0 && n & (n - 1) == 0
}

/// Bounded history of observed blocks, structure of arrays, power-of-two capacity.
// Only tests clone a ring, so the derived Clone stays unconstrained.
#[cfg_attr(
    verus_keep_ghost,
    verus_verify,
    verifier::allow(autoderive_clone_without_spec)
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BlockRing {
    numbers: Box<[u64]>,
    hashes: Box<[[u8; 32]]>,
    head: usize,
    len: usize,
}

#[cfg(verus_keep_ghost)]
verus! {

/// Masking with `w - 1` is reduction modulo `w` when `w` is a power of two.
proof fn lemma_mask_is_mod(x: usize, w: usize)
    by (bit_vector)
    requires
        w != 0,
        w & ((w - 1) as usize) == 0,
    ensures
        x & ((w - 1) as usize) == x % w,
        x % w < w,
{
}

/// Below `2w`, masking with `w - 1` wraps at most once.
proof fn lemma_mask_wraps(x: usize, w: usize)
    by (bit_vector)
    requires
        w != 0,
        w & ((w - 1) as usize) == 0,
        w <= 0x10_0000,
        x < w + w,
    ensures
        x & ((w - 1) as usize) == if x < w {
            x
        } else {
            (x - w) as usize
        },
{
}

/// `floor(log2 n) + 1` bounds `p` when `2^(p-1) <= n` (the bisection probe bound).
proof fn lemma_probe_bound(p: nat, n: int)
    requires
        p > 0 ==> pow2((p - 1) as nat) <= n,
        n >= 0,
    ensures
        p <= log(2, n) + 1,
{
    lemma_log_nonnegative(2, n);
    if p > 0 {
        let e = (p - 1) as nat;
        lemma_pow2(e);
        lemma_log_pow(2, e);
        lemma_log_is_ordered(2, pow2(e) as int, n);
        assert(log(2, pow2(e) as int) == e);
    }
}

impl BlockRing {
    pub(crate) closed spec fn cap(&self) -> int {
        self.numbers@.len() as int
    }

    /// Physical slot of a logical (oldest-first) index below the capacity.
    spec fn slot(&self, logical: int) -> int {
        if self.head + logical < self.cap() {
            self.head + logical
        } else {
            self.head + logical - self.cap()
        }
    }

    /// Well-formedness: power-of-two capacity within the engine's bounds, and
    /// numbers strictly ascending oldest-first.
    pub(crate) closed spec fn wf(&self) -> bool {
        &&& self.hashes@.len() == self.cap()
        &&& 2 <= self.cap() <= 0x10_0000
        &&& (self.cap() as usize) & ((self.cap() - 1) as usize) == 0
        &&& self.head < self.cap()
        &&& self.len <= self.cap()
        &&& forall|i: int, j: int|
            #![trigger self@[i], self@[j]]
            0 <= i < j < self.len ==> self@[i].number < self@[j].number
    }
}

impl BlockRing {
    /// Ascending numbers name at most one entry.
    proof fn lemma_index_unique(&self, k: int)
        requires
            self.wf(),
            0 <= k < self@.len(),
        ensures
            forall|i: int|
                0 <= i < self@.len() && #[trigger] self@[i].number == self@[k].number ==> i == k,
    {
        assert forall|i: int|
            0 <= i < self@.len() && #[trigger] self@[i].number == self@[k].number implies i == k by {
            if i < k {
                assert(self@[i].number < self@[k].number);
            } else if k < i {
                assert(self@[k].number < self@[i].number);
            }
        }
    }
}

impl View for BlockRing {
    type V = Seq<BlockRef>;

    closed spec fn view(&self) -> Seq<BlockRef> {
        Seq::new(
            self.len as nat,
            |i: int| BlockRef { number: self.numbers@[self.slot(i)], hash: self.hashes@[self.slot(i)] },
        )
    }
}

} // verus!

#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl BlockRing {
    /// Capacity must be a power of two; enforced by EngineConfig validation.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            2 <= capacity <= 0x10_0000,
            capacity & ((capacity - 1) as usize) == 0,
        ensures
            r.wf(),
            r.cap() == capacity,
            r@.len() == 0,
    ))]
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        debug_assert!(
            is_power_of_two(capacity),
            "BlockRing capacity must be a power of two"
        );
        Self {
            numbers: vec![0u64; capacity].into_boxed_slice(),
            hashes: vec![[0u8; 32]; capacity].into_boxed_slice(),
            head: 0,
            len: 0,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == self.cap()))]
    #[inline]
    pub(crate) fn capacity(&self) -> usize {
        self.numbers.len()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
            logical < self.cap(),
        ensures
            r == self.slot(logical as int),
            r < self.cap(),
    ))]
    #[inline]
    fn physical(&self, logical: usize) -> usize {
        #[cfg(verus_keep_ghost)]
        proof! {
            lemma_mask_wraps((self.head + logical) as usize, self.cap() as usize);
        }
        (self.head + logical) & (self.capacity() - 1)
    }

    /// Pushes a block with number strictly above the newest; overwrites the oldest when full.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).wf(),
            old(self)@.len() == 0 || old(self)@.last().number < block.number,
        ensures
            final(self).wf(),
            final(self).cap() == old(self).cap(),
            final(self)@ == ring_push(old(self)@, old(self).cap(), block),
    ))]
    pub(crate) fn push(&mut self, block: BlockRef) {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost pre = self@;
        }
        let capacity = self.capacity();
        if self.len < capacity {
            let index = self.physical(self.len);
            self.numbers[index] = block.number;
            self.hashes[index] = block.hash;
            self.len += 1;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(self@ =~= pre.push(block));
            }
        } else {
            let index = self.head;
            self.numbers[index] = block.number;
            self.hashes[index] = block.hash;
            #[cfg(verus_keep_ghost)]
            proof! {
                lemma_mask_wraps((self.head + 1) as usize, capacity);
            }
            self.head = (self.head + 1) & (capacity - 1);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(self@ =~= pre.drop_first().push(block));
            }
        }
    }

    /// Number of the newest entry, without reading the hash lane.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            r == if self@.len() == 0 {
                None
            } else {
                Some(self@.last().number)
            },
    ))]
    #[inline]
    pub(crate) fn newest_number(&self) -> Option<u64> {
        let newest = self.len.checked_sub(1)?;
        Some(self.numbers[self.physical(newest)])
    }

    /// Oldest-first access; index must be below len.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
            index < self@.len(),
        ensures
            r == self@[index as int],
    ))]
    #[inline]
    pub(crate) fn get(&self, index: usize) -> BlockRef {
        let physical = self.physical(index);
        BlockRef {
            number: self.numbers[physical],
            hash: self.hashes[physical],
        }
    }

    /// Hash for an exact number if still observed.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            r is Some <==> observes(self@, number),
            forall|i: int|
                0 <= i < self@.len() && #[trigger] self@[i].number == number
                    ==> r == Some(self@[i].hash),
    ))]
    pub(crate) fn hash_at(&self, number: u64) -> Option<[u8; 32]> {
        let logical = self.index_of(number)?;
        Some(self.hashes[self.physical(logical)])
    }

    /// Logical index of an exact number.
    ///
    /// Numbers ascend by at least one per entry, so the tip-relative guess is the
    /// highest index the number can sit at; a gapped chain falls back to the search.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            match r {
                Some(i) => i < self@.len() && self@[i as int].number == number,
                None => !observes(self@, number),
            },
            forall|i: int|
                0 <= i < self@.len() && #[trigger] self@[i].number == number
                    ==> r == Some(i as usize),
    ))]
    fn index_of(&self, number: u64) -> Option<usize> {
        let newest = self.len.checked_sub(1)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|i: int| 0 <= i < self@.len() implies #[trigger] self@[i].number
                <= self@[newest as int].number by {
                if i < newest {
                    assert(self@[i].number < self@[newest as int].number);
                }
            }
        }
        let behind = self.numbers[self.physical(newest)].checked_sub(number)?;
        let guess = match usize::try_from(behind) {
            Ok(behind) if behind <= newest => newest - behind,
            _ => 0,
        };
        if self.numbers[self.physical(guess)] == number {
            #[cfg(verus_keep_ghost)]
            proof! {
                self.lemma_index_unique(guess as int);
            }
            return Some(guess);
        }
        let logical = self.index_at_or_below(number)?;
        if self.numbers[self.physical(logical)] == number {
            Some(logical)
        } else {
            None
        }
    }

    /// Drops entries with a number strictly above the argument.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).cap() == old(self).cap(),
            prefix_at_or_below(old(self)@, number, final(self)@.len() as int),
            final(self)@ == old(self)@.subrange(0, final(self)@.len() as int),
    ))]
    #[cold]
    pub(crate) fn truncate_above(&mut self, number: u64) {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost pre = self@;
        }
        self.len = match self.index_at_or_below(number) {
            Some(logical) => logical + 1,
            None => 0,
        };
        if self.len == 0 {
            self.head = 0;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(self@ =~= pre.subrange(0, self.len as int));
        }
    }

    /// Logical index of the newest entry at or below the argument.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            match r {
                None => forall|i: int| 0 <= i < self.len ==> #[trigger] self@[i].number > number,
                Some(i) => i < self.len && self@[i as int].number <= number
                    && forall|j: int| i < j < self.len ==> #[trigger] self@[j].number > number,
            },
            prefix_at_or_below(self@, number, match r {
                Some(i) => i + 1,
                None => 0,
            }),
    ))]
    fn index_at_or_below(&self, number: u64) -> Option<usize> {
        let newest = self.len.checked_sub(1)?;
        if self.numbers[self.physical(newest)] <= number {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|i: int| 0 <= i < newest implies #[trigger] self@[i].number
                    <= number by {
                    assert(self@[i].number < self@[newest as int].number);
                }
            }
            return Some(newest);
        }
        let mut low = 0usize;
        let mut high = newest;
        // Ghost probe count: the loop runs at most floor(log2 newest) + 1 times.
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost mut probes: nat = 0;
            lemma2_to64();
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.wf(),
                newest + 1 == self.len,
                low <= high <= newest,
                low > 0 ==> self@[low as int].number <= number,
                forall|j: int| high < j < self.len ==> #[trigger] self@[j].number > number,
                pow2(probes) * (high - low) <= newest,
                probes > 0 ==> pow2((probes - 1) as nat) <= newest,
            decreases high - low,
        ))]
        while low < high {
            // Upper midpoint, `low + gap.div_ceil(2)`, in one subtraction.
            let gap = high - low;
            let mid = high - gap / 2;
            if self.numbers[self.physical(mid)] <= number {
                low = mid;
            } else {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(self@[mid as int].number > number);
                }
                high = mid - 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                lemma_pow2_unfold(probes + 1);
                lemma_pow2_pos(probes);
                assert(pow2(probes + 1) * (high - low) <= newest) by (nonlinear_arith)
                    requires
                        pow2(probes + 1) == 2 * pow2(probes),
                        2 * (high - low) <= gap,
                        pow2(probes) * gap <= newest,
                ;
                assert(pow2(probes) <= newest) by (nonlinear_arith)
                    requires
                        gap >= 1,
                        pow2(probes) > 0,
                        pow2(probes) * gap <= newest,
                ;
                probes = probes + 1;
            }
        }
        // The loop ran at most floor(log2 len) + 1 times.
        #[cfg(verus_keep_ghost)]
        proof! {
            lemma_probe_bound(probes, newest as int);
            lemma_log_is_ordered(2, newest as int, self.len as int);
            assert(probes <= log(2, self.len as int) + 1);
        }
        if self.numbers[self.physical(low)] <= number {
            Some(low)
        } else {
            None
        }
    }

    /// Empties the ring, keeping the allocation; stale slots stay unreachable below len.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).cap() == old(self).cap(),
            final(self)@ == Seq::<BlockRef>::empty(),
    ))]
    pub(crate) fn clear(&mut self) {
        self.head = 0;
        self.len = 0;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(self@ =~= Seq::<BlockRef>::empty());
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            r@ == self@,
    ))]
    pub(crate) fn iter(&self) -> Observed<'_> {
        Observed {
            ring: self,
            next: 0,
            remaining: self.len,
        }
    }

    /// Number of observed blocks.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            r == self@.len(),
    ))]
    #[cfg(feature = "wincode")]
    pub(crate) fn len(&self) -> usize {
        self.len
    }

    /// Number of entries at or below the argument; they are the oldest ones.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            prefix_at_or_below(self@, number, r as int),
    ))]
    #[cfg(any(feature = "wincode", test))]
    pub(crate) fn len_at_or_below(&self, number: u64) -> usize {
        match self.index_at_or_below(number) {
            Some(logical) => logical + 1,
            None => 0,
        }
    }

    /// True when the exact number is still observed.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            r == observes(self@, number),
    ))]
    pub(crate) fn observes(&self, number: u64) -> bool {
        self.index_of(number).is_some()
    }

    /// Bisects for the length of the oldest-first prefix the source still confirms, so
    /// entry `lo - 1` is the deepest canonical block and 0 means none is. At most
    /// `floor(log2 len) + 1` `header_at` calls; a source error is returned as is.
    // This bisection's probes are the calls it appends to `sview_log`: `hist[k]` for
    // `k` from `old(source)`'s log length on, each one the view that answered that probe.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            ({
                let (from, hist) = (
                    sview_log::<S>(old(source)).len() as int,
                    sview_log::<S>(final(source)),
                );
                &&& from <= hist.len()
                &&& hist.subrange(0, from) == sview_log::<S>(old(source))
                // Probe bound, unconditional: at most floor(log2 len) + 1 calls.
                &&& hist.len() - from <= log(2, self@.len() as int) + 1
                &&& forall|k: int| from <= k < hist.len() ==> a1::<S, S::Event>(#[trigger] hist[k])
                &&& r matches Ok(lo) ==> {
                    &&& lo <= self@.len()
                    // Safety: a probe's view held `ring[lo - 1]`, so by `ring_chain` it
                    // holds `ring[..lo]` at every height it has.
                    &&& lo > 0 ==> exists|k: int|
                        from <= k < hist.len() && #[trigger] confirms(hist[k], self@[lo - 1])
                            && (ring_chain(self@) ==> forall|i: int|
                            0 <= i < lo && hist[k].contains_key(#[trigger] self@[i].number)
                                ==> hist[k][self@[i].number] == self@[i]) && (ring_chain(self@)
                            && down_closed(hist[k]) ==> forall|i: int|
                            0 <= i < lo ==> confirms(hist[k], #[trigger] self@[i]))
                    // A probe's view did not hold `ring[lo]`.
                    &&& lo < self@.len() ==> exists|k: int|
                        from <= k < hist.len() && !#[trigger] confirms(hist[k], self@[lo as int])
                    // Optimality: with one view for every probe, `lo` is the
                    // longest prefix that view confirms.
                    &&& forall|v: ChainView|
                        (forall|k: int| from <= k < hist.len() ==> #[trigger] hist[k] == v)
                            && down_closed(v) && ring_chain(self@) ==> confirmed_prefix(
                            self@,
                            v,
                            lo as int,
                        )
                }
            }),
    ))]
    pub(crate) fn canonical_prefix<S: Source>(
        &self,
        source: &mut S,
    ) -> Result<usize, S::Error> {
        let mut lo = 0usize;
        let mut hi = self.len;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost log0 = sview_log::<S>(source);
            let ghost from = log0.len() as int;
            // The probes that set `lo` (confirmed `lo - 1`) and `hi` (did not confirm `hi`).
            let ghost mut lo_k: int = 0;
            let ghost mut hi_k: int = 0;
            lemma2_to64();
            assert(pow2(0) * self.len == self.len);
            assert(sview_log::<S>(source).subrange(0, from) =~= log0);
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self.wf(),
                lo <= hi <= self.len,
                log0 == sview_log::<S>(old(source)),
                from == log0.len(),
                from <= sview_log::<S>(source).len(),
                sview_log::<S>(source).subrange(0, from) == log0,
                forall|k: int|
                    from <= k < sview_log::<S>(source).len() ==> a1::<S, S::Event>(
                        #[trigger] sview_log::<S>(source)[k],
                    ),
                lo > 0 ==> from <= lo_k < sview_log::<S>(source).len() && confirms(
                    sview_log::<S>(source)[lo_k],
                    self@[lo - 1],
                ),
                hi < self.len ==> from <= hi_k < sview_log::<S>(source).len() && !confirms(
                    sview_log::<S>(source)[hi_k],
                    self@[hi as int],
                ),
                pow2((sview_log::<S>(source).len() - from) as nat) * (hi - lo) <= self.len,
                sview_log::<S>(source).len() > from ==> pow2(
                    (sview_log::<S>(source).len() - from - 1) as nat,
                ) <= self.len,
            decreases hi - lo,
        ))]
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let physical = self.physical(mid);
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost pre = sview_log::<S>(source);
                let ghost p = (pre.len() - from) as nat;
                let ghost gap = hi - lo;
                lemma_pow2_pos(p);
                lemma_pow2_unfold(p + 1);
                assert(pow2(p) <= self.len) by (nonlinear_arith)
                    requires
                        hi - lo >= 1,
                        pow2(p) * (hi - lo) <= self.len,
                ;
                // Counts this probe, so it also bounds a `?` exit.
                lemma_probe_bound(p + 1, self.len as int);
            }
            let confirmed = match source.header_at(self.numbers[physical])? {
                Some(header) => header.hash == self.hashes[physical],
                None => false,
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                broadcast use vstd::array::group_array_axioms;
                let post = sview_log::<S>(source);
                let v = post.last();
                assert(post.subrange(0, from) =~= pre.subrange(0, from));
                if confirmed {
                    assert(v[self@[mid as int].number].hash =~= self@[mid as int].hash);
                    assert(confirms(v, self@[mid as int]));
                    lo_k = pre.len() as int;
                } else {
                    hi_k = pre.len() as int;
                }
            }
            if confirmed {
                lo = mid + 1;
            } else {
                hi = mid;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(pow2(p + 1) * (hi - lo) <= self.len) by (nonlinear_arith)
                    requires
                        pow2(p + 1) == 2 * pow2(p),
                        2 * (hi - lo) <= gap,
                        pow2(p) * gap <= self.len,
                ;
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            lemma_probe_bound((sview_log::<S>(source).len() - from) as nat, self.len as int);
        }
        Ok(lo)
    }
}

/// Oldest-first iterator over observed blocks.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct Observed<'a> {
    ring: &'a BlockRing,
    next: usize,
    remaining: usize,
}

#[cfg(verus_keep_ghost)]
verus! {

impl<'a> View for Observed<'a> {
    type V = Seq<BlockRef>;

    /// The blocks still to come, oldest first.
    closed spec fn view(&self) -> Seq<BlockRef> {
        self.ring@.subrange(self.next as int, self.next + self.remaining)
    }
}

impl<'a> Observed<'a> {
    /// Holds between field writes in `next` (it lowers `remaining` first), so it is a
    /// type invariant.
    #[verifier::type_invariant]
    spec fn inv(&self) -> bool {
        &&& self.ring.wf()
        &&& self.next + self.remaining <= self.ring@.len()
    }
}

} // verus!

// The yielded sequence is `Observed@`, fixed by `iter`. tcb.rs opts `Observed` out of
// vstd's iterator laws, so this verifies panic- and overflow-free only.
#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl<'a> Iterator for Observed<'a> {
    type Item = BlockRef;

    fn next(&mut self) -> Option<Self::Item> {
        #[cfg(verus_keep_ghost)]
        proof! {
            use_type_invariant(&*self);
        }
        if self.remaining == 0 {
            return None;
        }
        let block = self.ring.get(self.next);
        self.remaining -= 1;
        self.next += 1;
        Some(block)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        #[cfg(verus_keep_ghost)]
        proof! {
            use_type_invariant(self);
        }
        (self.remaining, Some(self.remaining))
    }
}

impl ExactSizeIterator for Observed<'_> {}

#[cfg(test)]
mod tests {
    use super::BlockRing;
    use crate::{
        position::BlockRef,
        source::Source,
    };
    #[cfg(not(feature = "std"))]
    use alloc::{
        vec,
        vec::Vec,
    };
    #[cfg(feature = "std")]
    use std::{
        vec,
        vec::Vec,
    };

    fn block(number: u64) -> BlockRef {
        let mut hash = [0u8; 32];
        hash[..8].copy_from_slice(&number.to_le_bytes());
        BlockRef { number, hash }
    }

    #[test]
    fn push_and_newest_round_trip() {
        // given three pushed blocks
        let mut ring = BlockRing::with_capacity(4);
        ring.push(block(1));
        ring.push(block(2));
        ring.push(block(3));
        // when reading newest
        let newest = ring.iter().last();
        // then the last push returns
        assert_eq!(newest, Some(block(3)));
    }

    #[test]
    fn wraparound_overwrites_oldest() {
        // given capacity 4 and six pushes
        let mut ring = BlockRing::with_capacity(4);
        for number in 1..=6 {
            ring.push(block(number));
        }
        // when iterating
        let observed: Vec<BlockRef> = ring.iter().collect();
        // then exactly the last four blocks appear oldest-first
        assert_eq!(observed, vec![block(3), block(4), block(5), block(6)]);
    }

    #[test]
    fn hash_at_finds_only_retained_numbers() {
        // given a wrapped ring
        let mut ring = BlockRing::with_capacity(4);
        for number in 1..=6 {
            ring.push(block(number));
        }
        // when querying an evicted number
        let evicted = ring.hash_at(2);
        // then None; a retained number returns its hash
        assert_eq!(evicted, None);
        assert_eq!(ring.hash_at(5), Some(block(5).hash));
    }

    #[test]
    fn hash_at_finds_numbers_across_a_gapped_ring() {
        // given a ring whose numbers skip, defeating the tip-relative guess
        let mut ring = BlockRing::with_capacity(8);
        for number in [1u64, 2, 5, 9, 10, 40] {
            ring.push(block(number));
        }
        // when querying each stored number and two absent ones
        let found: Vec<Option<[u8; 32]>> = [1u64, 2, 5, 9, 10, 40, 3, 39]
            .iter()
            .map(|n| ring.hash_at(*n))
            .collect();
        // then every stored number resolves and the gaps stay absent
        assert_eq!(
            found[..6],
            [1u64, 2, 5, 9, 10, 40].map(|n| Some(block(n).hash))
        );
        assert_eq!(found[6], None);
        assert_eq!(found[7], None);
    }

    #[test]
    fn hash_at_rejects_numbers_above_the_tip() {
        // given a ring topping out at block 3
        let mut ring = BlockRing::with_capacity(4);
        for number in 1..=3 {
            ring.push(block(number));
        }
        // when querying above the tip and on an empty ring
        let above = ring.hash_at(4);
        let empty = BlockRing::with_capacity(4).hash_at(1);
        // then both are absent
        assert_eq!(above, None);
        assert_eq!(empty, None);
    }

    #[test]
    fn truncate_above_keeps_the_prefix_at_or_below() {
        // given a wrapped ring holding blocks 3 through 6
        let mut ring = BlockRing::with_capacity(4);
        for number in 1..=6 {
            ring.push(block(number));
        }
        // when truncating above block 4
        ring.truncate_above(4);
        // then only blocks 3 and 4 remain, newest first at 4
        assert_eq!(ring.iter().collect::<Vec<_>>(), vec![block(3), block(4)]);
        assert_eq!(ring.iter().last(), Some(block(4)));
    }

    #[test]
    fn truncate_above_empties_when_every_entry_is_higher() {
        // given a ring holding blocks 3 through 6
        let mut ring = BlockRing::with_capacity(4);
        for number in 1..=6 {
            ring.push(block(number));
        }
        // when truncating below everything observed
        ring.truncate_above(2);
        // then the ring is empty and accepts pushes again
        assert_eq!(ring.iter().len(), 0);
        ring.push(block(9));
        assert_eq!(ring.iter().last(), Some(block(9)));
    }

    #[test]
    fn len_at_or_below_counts_the_matching_prefix() {
        // given a gapped ring
        let mut ring = BlockRing::with_capacity(8);
        for number in [2u64, 4, 7, 11] {
            ring.push(block(number));
        }
        // when counting at or below a number between entries
        let prefix: Vec<BlockRef> = ring.iter().take(ring.len_at_or_below(9)).collect();
        // then the entries up to and including 7 are counted, oldest first
        assert_eq!(prefix, vec![block(2), block(4), block(7)]);
        assert_eq!(ring.len_at_or_below(1), 0);
        assert_eq!(ring.len_at_or_below(11), 4);
    }

    #[test]
    fn observes_reports_exact_membership() {
        // given a ring holding blocks 3 through 6
        let mut ring = BlockRing::with_capacity(4);
        for number in 1..=6 {
            ring.push(block(number));
        }
        // when asking about a retained and an evicted number
        let retained = ring.observes(4);
        let evicted = ring.observes(2);
        // then only the retained one is observed
        assert!(retained);
        assert!(!evicted);
    }

    /// Answers `header_at` from a fixed view, counting calls and failing the numbered one.
    struct View {
        canonical: Vec<BlockRef>,
        calls: u32,
        fail_on: Option<u32>,
    }

    impl View {
        /// A view that confirms entry `i` of `ring` exactly when bit `i` of `mask` is set.
        /// Unconfirmed entries alternate between a forked hash and a missing header.
        fn of(ring: &BlockRing, mask: u32) -> Self {
            let canonical = ring
                .iter()
                .enumerate()
                .filter_map(|(i, block)| match ((mask >> i) & 1, i % 2) {
                    (1, _) => Some(block),
                    (_, 0) => Some(BlockRef {
                        hash: [0xff; 32],
                        ..block
                    }),
                    _ => None,
                })
                .collect();
            Self {
                canonical,
                calls: 0,
                fail_on: None,
            }
        }
    }

    impl Source for View {
        type Error = u32;
        type Event = ();

        fn head(&mut self) -> Result<u64, u32> {
            Ok(0)
        }

        fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, u32> {
            self.calls += 1;
            if self.fail_on == Some(self.calls) {
                return Err(self.calls);
            }
            Ok(self.canonical.iter().copied().find(|b| b.number == number))
        }

        fn events_in(
            &mut self,
            _from: u64,
            _to: u64,
            _out: &mut Vec<(BlockRef, u32, ())>,
        ) -> Result<(), u32> {
            Ok(())
        }
    }

    /// Rings of every length up to `capacity`, wrapped first so logical and physical
    /// indices differ, and gapped so numbers and indices differ.
    fn rings(capacity: usize) -> impl Iterator<Item = BlockRing> {
        (0..=capacity).map(move |len| {
            let mut ring = BlockRing::with_capacity(capacity);
            for number in 0..(capacity + len) as u64 {
                ring.push(block(3 * number + 1));
            }
            ring.truncate_above(len.checked_sub(1).map_or(0, |i| ring.get(i).number));
            ring
        })
    }

    #[test]
    fn canonical_prefix_probes_at_most_log2_len_plus_one_times() {
        for ring in rings(16) {
            let len = ring.iter().len();
            let bound = if len == 0 { 0 } else { len.ilog2() + 1 };
            for mask in 0..1u32 << len {
                // given any confirmation pattern over the ring, not only a prefix
                let mut view = View::of(&ring, mask);
                // when bisecting
                let lo = ring.canonical_prefix(&mut view).unwrap();
                // then the probe count stays within the bound, and lo sits on a
                // confirmed-to-unconfirmed boundary
                assert!(
                    view.calls <= bound,
                    "len {len} mask {mask:b}: {} calls",
                    view.calls
                );
                assert!(
                    lo == 0 || (mask >> (lo - 1)) & 1 == 1,
                    "len {len} mask {mask:b}"
                );
                assert!(
                    lo == len || (mask >> lo) & 1 == 0,
                    "len {len} mask {mask:b}"
                );
            }
        }
    }

    #[test]
    fn canonical_prefix_is_the_deepest_canonical_entry_of_one_view() {
        for ring in rings(8) {
            let len = ring.iter().len();
            for k in 0..=len {
                // given one view in which exactly the oldest k entries are canonical
                let mut view = View::of(&ring, (1u32 << k) - 1);
                // when bisecting
                let lo = ring.canonical_prefix(&mut view).unwrap();
                // then the prefix is exactly k long, so entry k - 1 is the deepest match
                assert_eq!(lo, k, "len {len}");
            }
        }
    }

    #[test]
    fn canonical_prefix_passes_a_source_error_through_unchanged() {
        let ring = rings(8).nth(8).unwrap();
        let mut clean = View::of(&ring, 0b0111);
        ring.canonical_prefix(&mut clean).unwrap();
        for fail_on in 1..=clean.calls {
            // given a source that fails on its nth probe
            let before = ring.clone();
            let mut view = View::of(&ring, 0b0111);
            view.fail_on = Some(fail_on);
            // when bisecting
            let result = ring.canonical_prefix(&mut view);
            // then that error comes back, no probe follows it, and the ring is unchanged
            assert_eq!(result, Err(fail_on));
            assert_eq!(view.calls, fail_on);
            assert_eq!(ring, before);
        }
    }

    #[test]
    fn clone_is_independent() {
        // given a cloned ring
        let mut ring = BlockRing::with_capacity(4);
        ring.push(block(1));
        let clone = ring.clone();
        // when pushing to the original
        ring.push(block(2));
        // then the clone is unchanged
        assert_eq!(clone.iter().last(), Some(block(1)));
        assert_eq!(ring.iter().last(), Some(block(2)));
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl BlockRing {
    /// The view-level facts of `wf`, for modules that cannot see its body.
    pub(crate) proof fn lemma_wf(&self)
        requires
            self.wf(),
        ensures
            self@.len() <= self.cap(),
            2 <= self.cap() <= 0x10_0000,
            (self.cap() as usize) & ((self.cap() - 1) as usize) == 0,
            crate::verus::model::ring_ascending(self@),
    {
    }
}
} // verus!
