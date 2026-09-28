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
use vstd::{
    arithmetic::power2::{
        lemma_pow2_pos,
        lemma_pow2_unfold,
        lemma2_to64,
        pow2,
    },
    prelude::*,
};

use crate::{
    position::BlockRef,
    source::Source,
};

/// True when `n` is a power of two; spelled out rather than std's so the verifier can state it.
pub(crate) const fn is_power_of_two(n: usize) -> bool {
    n != 0 && n & (n - 1) == 0
}

/// Bounded history of observed blocks, structure of arrays, power-of-two capacity.
// Clone gets its spec with the ring proofs (P4); until then clones are unconstrained.
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

impl BlockRing {
    pub(crate) closed spec fn cap(&self) -> int {
        self.numbers@.len() as int
    }

    /// Physical slot of a logical (oldest-first) index.
    spec fn slot(&self, logical: int) -> int {
        (self.head + logical) % self.cap()
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

impl BlockRing {
    /// Capacity must be a power of two; enforced by EngineConfig validation.
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
            lemma_mask_is_mod((self.head + logical) as usize, self.cap() as usize);
        }
        (self.head + logical) & (self.capacity() - 1)
    }

    /// Pushes a block with number strictly above the newest; overwrites the oldest when full.
    pub(crate) fn push(&mut self, block: BlockRef) {
        let capacity = self.capacity();
        if self.len < capacity {
            let index = self.physical(self.len);
            self.numbers[index] = block.number;
            self.hashes[index] = block.hash;
            self.len += 1;
        } else {
            let index = self.head;
            self.numbers[index] = block.number;
            self.hashes[index] = block.hash;
            self.head = (self.head + 1) & (capacity - 1);
        }
    }

    /// Number of the newest entry, without reading the hash lane.
    #[inline]
    pub(crate) fn newest_number(&self) -> Option<u64> {
        let newest = self.len.checked_sub(1)?;
        Some(self.numbers[self.physical(newest)])
    }

    /// Oldest-first access; index must be below len.
    #[inline]
    pub(crate) fn get(&self, index: usize) -> BlockRef {
        let physical = self.physical(index);
        BlockRef {
            number: self.numbers[physical],
            hash: self.hashes[physical],
        }
    }

    /// Hash for an exact number if still observed.
    pub(crate) fn hash_at(&self, number: u64) -> Option<[u8; 32]> {
        let logical = self.index_of(number)?;
        Some(self.hashes[self.physical(logical)])
    }

    /// Logical index of an exact number.
    ///
    /// Numbers ascend by at least one per entry, so the tip-relative guess is the
    /// highest index the number can sit at; a gapped chain falls back to the search.
    fn index_of(&self, number: u64) -> Option<usize> {
        let newest = self.len.checked_sub(1)?;
        let behind = self.numbers[self.physical(newest)].checked_sub(number)?;
        let guess = match usize::try_from(behind) {
            Ok(behind) if behind <= newest => newest - behind,
            _ => 0,
        };
        if self.numbers[self.physical(guess)] == number {
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
    #[cold]
    pub(crate) fn truncate_above(&mut self, number: u64) {
        self.len = match self.index_at_or_below(number) {
            Some(logical) => logical + 1,
            None => 0,
        };
        if self.len == 0 {
            self.head = 0;
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
    ))]
    fn index_at_or_below(&self, number: u64) -> Option<usize> {
        let newest = self.len.checked_sub(1)?;
        if self.numbers[self.physical(newest)] <= number {
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
            // `div_ceil` has no vstd spec; this is its definition.
            let gap = high - low;
            let mid = low + (gap / 2 + gap % 2);
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
        if self.numbers[self.physical(low)] <= number {
            Some(low)
        } else {
            None
        }
    }

    /// Empties the ring, keeping the allocation; stale slots stay unreachable below len.
    pub(crate) fn clear(&mut self) {
        self.head = 0;
        self.len = 0;
    }

    pub(crate) fn iter(&self) -> Observed<'_> {
        Observed {
            ring: self,
            next: 0,
            remaining: self.len,
        }
    }

    /// Oldest-first iterator over the entries at or below the argument.
    #[cfg(any(feature = "wincode", test))]
    pub(crate) fn iter_at_or_below(&self, number: u64) -> Observed<'_> {
        Observed {
            ring: self,
            next: 0,
            remaining: match self.index_at_or_below(number) {
                Some(logical) => logical + 1,
                None => 0,
            },
        }
    }

    /// True when the exact number is still observed.
    pub(crate) fn observes(&self, number: u64) -> bool {
        self.index_of(number).is_some()
    }

    /// Bisects for the length of the oldest-first prefix the source still confirms, so
    /// entry `lo - 1` is the deepest canonical block and 0 means none is. At most
    /// `floor(log2 len) + 1` `header_at` calls; a source error is returned as is.
    pub(crate) fn canonical_prefix<S: Source>(
        &self,
        source: &mut S,
    ) -> Result<usize, S::Error> {
        let mut lo = 0usize;
        let mut hi = self.len;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let physical = self.physical(mid);
            let confirmed = match source.header_at(self.numbers[physical])? {
                Some(header) => header.hash == self.hashes[physical],
                None => false,
            };
            if confirmed {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        Ok(lo)
    }
}

/// Oldest-first iterator over observed blocks.
pub struct Observed<'a> {
    ring: &'a BlockRing,
    next: usize,
    remaining: usize,
}

impl<'a> Iterator for Observed<'a> {
    type Item = BlockRef;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let block = self.ring.get(self.next);
        self.next += 1;
        self.remaining -= 1;
        Some(block)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
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
    fn iter_at_or_below_yields_the_matching_prefix() {
        // given a gapped ring
        let mut ring = BlockRing::with_capacity(8);
        for number in [2u64, 4, 7, 11] {
            ring.push(block(number));
        }
        // when iterating at or below a number between entries
        let prefix: Vec<BlockRef> = ring.iter_at_or_below(9).collect();
        // then the entries up to and including 7 appear, oldest first
        assert_eq!(prefix, vec![block(2), block(4), block(7)]);
        assert_eq!(ring.iter_at_or_below(1).count(), 0);
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
