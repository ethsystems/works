#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use core::fmt;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use crate::position::BlockRef;
#[cfg(verus_keep_ghost)]
use crate::position::Position;
#[cfg(verus_keep_ghost)]
use crate::verus::model::{
    BatchView,
    lt,
    lt_sorted,
};
#[cfg(verus_keep_ghost)]
use vstd::{
    laws_cmp::obeys_cmp,
    std_specs::{
        cmp::{
            OrdSpec,
            PartialOrdIs,
            PartialOrdSpec,
        },
        iter::IteratorSpec,
    },
};

/// One block's events within a batch.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug)]
pub struct SpanView<'a, E> {
    /// Number of the block the events belong to.
    pub number: u64,
    /// Hash of the block the events belong to.
    pub hash: &'a [u8; 32],
    /// Log index of each event within the block, strictly ascending.
    pub log_indices: &'a [u32],
    /// Consumer events, parallel to `log_indices`.
    pub events: &'a [E],
}

impl<E> SpanView<'_, E> {
    /// Owned header of the span's block.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r == (BlockRef { number: self.number, hash: *self.hash }),
    ))]
    pub fn block(&self) -> BlockRef {
        BlockRef {
            number: self.number,
            hash: *self.hash,
        }
    }
}

/// One poll's worth of events
#[cfg_attr(
    verus_keep_ghost,
    verus_verify,
    verifier::allow(autoderive_clone_without_spec)
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Batch<E> {
    /// Refetched header of the cursor block; None means the source could not produce it.
    pub boundary: Option<BlockRef>,
    // pub(crate) so the verifier can read `boundary` outside this module: it treats a
    // struct as opaque wherever its most private field is invisible, pub fields included.
    pub(crate) blocks: Vec<u64>,
    pub(crate) hashes: Vec<[u8; 32]>,
    pub(crate) ends: Vec<usize>,
    pub(crate) log_indices: Vec<u32>,
    pub(crate) events: Vec<E>,
}

#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl<E> Batch<E> {
    /// Builds an empty, capacity-free batch.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r@.wf(),
            r@.ends.len() == 0,
            r@.boundary is None,
    ))]
    pub fn new() -> Self {
        Self {
            boundary: None,
            blocks: Vec::new(),
            hashes: Vec::new(),
            ends: Vec::new(),
            log_indices: Vec::new(),
            events: Vec::new(),
        }
    }

    /// Empties every lane and the boundary while keeping capacity.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures
            final(self)@.wf(),
            final(self)@.ends.len() == 0,
            final(self)@.boundary is None,
    ))]
    pub fn clear(&mut self) {
        self.boundary = None;
        self.blocks.clear();
        self.hashes.clear();
        self.ends.clear();
        self.log_indices.clear();
        self.events.clear();
    }

    /// True when the batch carries no spans.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == (self@.ends.len() == 0)))]
    pub fn is_empty(&self) -> bool {
        self.ends.is_empty()
    }

    /// Spans the batch carries, one per observed block.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == self@.ends.len()))]
    pub fn span_count(&self) -> usize {
        self.ends.len()
    }

    /// Appends one block's complete event set in log order.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self)@.wf(),
            finite_into_iter(events),
        ensures
            pushed_block(old(self)@, final(self)@, block),
            final(self)@.boundary == old(self)@.boundary,
    ))]
    pub fn push_block(
        &mut self,
        block: BlockRef,
        events: impl IntoIterator<Item = (u32, E)>,
    ) {
        self.blocks.push(block.number);
        self.hashes.push(block.hash);
        let mut events = events.into_iter();
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost mid = self@;
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self@.blocks == mid.blocks,
                self@.hashes == mid.hashes,
                self@.ends == mid.ends,
                self@.log_indices.len() - mid.log_indices.len()
                    == self@.events.len() - mid.events.len(),
                self@.log_indices.len() >= mid.log_indices.len(),
                self@.events.len() >= mid.events.len(),
                self@.log_indices.subrange(0, mid.log_indices.len() as int) == mid.log_indices,
                self@.events.subrange(0, mid.events.len() as int) == mid.events,
                self.boundary == old(self).boundary,
                events.obeys_prophetic_iter_laws(),
                events.decrease() is Some,
            decreases events.decrease()->0,
        ))]
        #[expect(
            clippy::while_let_loop,
            reason = "loop and match is the form Verus verifies"
        )]
        loop {
            match events.next() {
                Some((log_index, event)) => {
                    self.log_indices.push(log_index);
                    self.events.push(event);
                }
                None => break,
            }
        }
        self.ends.push(self.events.len());
    }

    /// Span `i`, oldest first, whose events begin at `start`: the previous span's end, or
    /// 0 for the first. `i` must be below `span_count`.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self@.wf(),
            i < self@.ends.len(),
            start == self@.start(i as int),
        ensures
            r.number == self@.blocks[i as int],
            *r.hash == self@.hashes[i as int],
            r.log_indices@ == self@.log_indices.subrange(start as int, self@.ends[i as int] as int),
            r.events@ == self@.events.subrange(start as int, self@.ends[i as int] as int),
            span_matches(self@, i as int, r),
    ))]
    pub(crate) fn span(&self, i: usize, start: usize) -> SpanView<'_, E> {
        let end = self.ends[i];
        SpanView {
            number: self.blocks[i],
            hash: &self.hashes[i],
            log_indices: &self.log_indices[start..end],
            events: &self.events[start..end],
        }
    }

    /// Iterates spans oldest first with their event slices.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self@.wf(),
    ))]
    pub fn spans(&self) -> Spans<'_, E> {
        Spans {
            batch: self,
            next: 0,
            start: 0,
        }
    }

    /// Validates the orderings a source controls, before any event reaches the fold.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self@.wf(),
        ensures
            r is Ok <==> self@.shaped(),
            r is Ok ==> lt_sorted(self@.flat()),
            validate_names_first(self@, r),
    ))]
    pub fn validate(&self) -> Result<(), BatchShapeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            lemma_int_laws();
        }
        if let Some(span) = first_descent(&self.blocks) {
            #[cfg(verus_keep_ghost)]
            proof! {
                if self@.shaped() {
                    assert(self@.blocks[span - 1] < self@.blocks[span as int]);
                }
            }
            return Err(BatchShapeError::BlocksNotAscending { span });
        }
        let mut start = 0usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self@.wf(),
                ascending_upto(self@.blocks, self@.blocks.len() as int),
                span <= self@.ends.len(),
                start == self@.start(span as int),
                spans_ok_upto(self@, span as int),
        ))]
        for span in 0..self.ends.len() {
            let end = self.ends[span];
            #[cfg(verus_keep_ghost)]
            proof! {
                lemma_end_bounds(self@, span as int);
                lemma_int_laws();
            }
            if end <= start {
                #[cfg(verus_keep_ghost)]
                proof! {
                    if self@.shaped() {
                        assert(self@.start(span as int) < self@.ends[span as int]);
                    }
                }
                return Err(BatchShapeError::SpanEmpty { span });
            }
            if let Some(offset) = first_descent(&self.log_indices[start..end]) {
                #[cfg(verus_keep_ghost)]
                proof! {
                    lemma_log_descent_unshaped(self@, span as int, offset);
                }
                return Err(BatchShapeError::LogIndexNotAscending {
                    span,
                    index: start + offset,
                });
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                lemma_span_passes(self@, span as int);
            }
            start = end;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            lemma_int_laws();
            lemma_ascending_pairwise(self@.blocks);
            lemma_spans_ok_shaped(self@);
            lemma_shaped_sorted(self@);
        }
        Ok(())
    }

    /// Appends one block's span by popping the tail of `entries` while it belongs to
    /// `block`, so entries sorted by descending log index come out in log order.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            old(self)@.wf(),
        ensures
            pushed_block(old(self)@, final(self)@, block),
            final(self)@.boundary == old(self)@.boundary,
            popped_tail(old(self)@, final(self)@, old(entries)@, final(entries)@, block),
    ))]
    pub(crate) fn push_block_from_tail(
        &mut self,
        block: BlockRef,
        entries: &mut Vec<(BlockRef, u32, E)>,
    ) {
        self.blocks.push(block.number);
        self.hashes.push(block.hash);
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost mid = self@;
            let ghost all = entries@;
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                self@.blocks == mid.blocks,
                self@.hashes == mid.hashes,
                self@.ends == mid.ends,
                self@.boundary == mid.boundary,
                self@.log_indices.len() - mid.log_indices.len()
                    == self@.events.len() - mid.events.len(),
                self@.events.len() - mid.events.len() == all.len() - entries@.len(),
                entries@.len() <= all.len(),
                self@.log_indices.subrange(0, mid.log_indices.len() as int) == mid.log_indices,
                self@.events.subrange(0, mid.events.len() as int) == mid.events,
                entries@ == all.subrange(0, entries@.len() as int),
                appended_reversed(mid, self@, all, all.len() - entries@.len(), block),
            ensures
                entries@.len() == 0 || entries@.last().0 != block,
            decreases entries@.len(),
        ))]
        loop {
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost e0 = entries@;
                let ghost s0 = self@;
            }
            match entries.last() {
                Some((tail, _, _)) if *tail == block => {}
                _ => break,
            }
            let Some((_, log_index, event)) = entries.pop() else {
                break;
            };
            self.log_indices.push(log_index);
            self.events.push(event);
            #[cfg(verus_keep_ghost)]
            proof! {
                let n = all.len() - e0.len();
                assert(all[all.len() - 1 - n] == e0.last());
                assert forall|j: int| 0 <= j < n + 1 implies #[trigger] appended_at(
                    mid,
                    self@,
                    all,
                    j,
                    block,
                ) by {
                    if j < n {
                        assert(appended_at(mid, s0, all, j, block));
                        assert(s0.events[mid.events.len() + j] == self@.events[mid.events.len() + j]);
                        assert(s0.log_indices[mid.log_indices.len() + j] == self@.log_indices[mid.log_indices.len() + j]);
                    }
                }
            }
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost done = self@;
        }
        self.ends.push(self.events.len());
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|j: int| 0 <= j < all.len() - entries@.len() implies #[trigger] appended_at(
                old(self)@,
                self@,
                all,
                j,
                block,
            ) by {
                assert(appended_at(mid, done, all, j, block));
            }
        }
    }
}

/// Index of the first element that does not exceed its predecessor.
///
/// The sweep is branchless so it vectorizes; the cold locate pass runs only on failure.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        obeys_cmp::<T>(),
    ensures
        descent_result(values@, r),
))]
pub(crate) fn first_descent<T: Ord>(values: &[T]) -> Option<usize> {
    let mut ascending = true;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(vstd::laws_cmp::obeys_cmp_partial_ord);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            T::obeys_partial_cmp_spec(),
            ascending <==> ascending_upto(values@, i as int),
    ))]
    for i in 1..values.len() {
        // A select, not `&=`: Verus rejects `&` on bool. It still vectorizes, see
        // tasks/chainfold-perf-p3.md.
        ascending = if values[i - 1] < values[i] {
            ascending
        } else {
            false
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(ascending_upto(values@, i + 1) <==> (ascending_upto(values@, i as int)
                && values@[i - 1].is_lt(&values@[i as int])));
        }
    }
    if ascending {
        return None;
    }
    locate_descent(values)
}

#[cold]
#[expect(clippy::manual_find, reason = "Verus has no spec for Iterator::find")]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        obeys_cmp::<T>(),
    ensures
        descent_result(values@, r),
))]
fn locate_descent<T: Ord>(values: &[T]) -> Option<usize> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(vstd::laws_cmp::obeys_cmp_partial_ord);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            obeys_cmp::<T>(),
            T::obeys_partial_cmp_spec(),
            ascending_upto(values@, i as int),
    ))]
    for i in 1..values.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            lemma_le_not_gt(values@[i as int], values@[i - 1]);
        }
        if values[i] <= values[i - 1] {
            return Some(i);
        }
    }
    None
}

/// Oldest-first iterator over a batch's spans.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug)]
pub struct Spans<'a, E> {
    batch: &'a Batch<E>,
    next: usize,
    start: usize,
}

#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl<'a, E> Iterator for Spans<'a, E> {
    type Item = SpanView<'a, E>;

    fn next(&mut self) -> Option<Self::Item> {
        #[cfg(verus_keep_ghost)]
        proof! {
            use_type_invariant(&*self);
        }
        let start = self.start;
        let end = *self.batch.ends.get(self.next)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(self.next < self.batch.ends.len());
            lemma_end_bounds(self.batch@, self.next as int);
            if self.next + 1 < self.batch@.ends.len() {
                assert(self.batch@.ends[self.next as int] <= self.batch@.ends[self.next + 1]);
            }
        }
        let number = self.batch.blocks[self.next];
        let hash = &self.batch.hashes[self.next];
        self.next += 1;
        self.start = end;
        Some(SpanView {
            number,
            hash,
            log_indices: &self.batch.log_indices[start..end],
            events: &self.batch.events[start..end],
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        #[cfg(verus_keep_ghost)]
        proof! {
            use_type_invariant(self);
        }
        let remaining = self.batch.ends.len() - self.next;
        (remaining, Some(remaining))
    }
}

impl<E> ExactSizeIterator for Spans<'_, E> {}

#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl<E> Default for Batch<E> {
    fn default() -> Self {
        Self::new()
    }
}

/// Batch layout violation found before any event reaches the fold.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BatchShapeError {
    /// Span carries no events; a block with none is left out of the batch.
    SpanEmpty {
        /// Index of the offending span.
        span: usize,
    },
    /// Span block number does not exceed its predecessor's.
    BlocksNotAscending {
        /// Index of the offending span.
        span: usize,
    },
    /// Log index does not exceed its predecessor's within a span.
    LogIndexNotAscending {
        /// Index of the offending span.
        span: usize,
        /// Index of the offending event in the batch's event lane.
        index: usize,
    },
}

impl fmt::Display for BatchShapeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SpanEmpty { span } => {
                write!(f, "span {span} carries no events")
            }
            Self::BlocksNotAscending { span } => {
                write!(f, "span {span} block number is not strictly ascending")
            }
            Self::LogIndexNotAscending { span, index } => {
                write!(
                    f,
                    "span {span} log index at event {index} is not strictly ascending"
                )
            }
        }
    }
}

impl core::error::Error for BatchShapeError {}

#[cfg(test)]
mod tests {
    use super::{
        Batch,
        BatchShapeError,
    };
    use crate::position::BlockRef;
    #[cfg(not(feature = "std"))]
    use alloc::vec::Vec;
    #[cfg(feature = "std")]
    use std::vec::Vec;

    fn block(number: u64) -> BlockRef {
        BlockRef {
            number,
            hash: [0; 32],
        }
    }

    /// Builds a batch from one (block number, log indices) pair per span.
    fn batch_of(spans: &[(u64, &[u32])]) -> Batch<u64> {
        let mut batch = Batch::new();
        for (number, indices) in spans {
            batch.push_block(
                block(*number),
                indices.iter().map(|index| (*index, u64::from(*index))),
            );
        }
        batch
    }

    #[test]
    fn valid_batch_passes_validation() {
        // given two spans covering four events
        let batch = batch_of(&[(1, &[0, 1]), (2, &[0, 1])]);
        // when validated
        let result = batch.validate();
        // then Ok
        assert_eq!(result, Ok(()));
    }

    #[test]
    fn batch_with_descending_blocks_fails() {
        // given spans at blocks 7 then 5
        let batch = batch_of(&[(7, &[0]), (5, &[0])]);
        // when validated
        let result = batch.validate();
        // then BlocksNotAscending at span 1
        assert_eq!(result, Err(BatchShapeError::BlocksNotAscending { span: 1 }));
    }

    #[test]
    fn batch_with_repeated_log_index_fails() {
        // given one span with log indices 3, 3
        let batch = batch_of(&[(1, &[3, 3])]);
        // when validated
        let result = batch.validate();
        // then LogIndexNotAscending at span 0, event index 1
        assert_eq!(
            result,
            Err(BatchShapeError::LogIndexNotAscending { span: 0, index: 1 })
        );
    }

    #[test]
    fn batch_with_an_eventless_span_fails() {
        // given a second span pushed with no events
        let batch = batch_of(&[(1, &[0]), (2, &[])]);
        // when validated
        let result = batch.validate();
        // then SpanEmpty at span 1
        assert_eq!(result, Err(BatchShapeError::SpanEmpty { span: 1 }));
    }

    #[test]
    fn spans_yield_their_own_event_slices() {
        // given three spans of differing width
        let batch = batch_of(&[(1, &[0, 1, 2]), (4, &[7]), (9, &[0, 5])]);
        // when iterating the spans
        let seen: Vec<(u64, Vec<u32>, Vec<u64>)> = batch
            .spans()
            .map(|span| (span.number, span.log_indices.to_vec(), span.events.to_vec()))
            .collect();
        // then each span carries exactly the events pushed with its block
        assert_eq!(
            seen,
            [
                (1, [0, 1, 2].to_vec(), [0u64, 1, 2].to_vec()),
                (4, [7].to_vec(), [7u64].to_vec()),
                (9, [0, 5].to_vec(), [0u64, 5].to_vec()),
            ]
        );
        assert_eq!(batch.spans().len(), batch.span_count());
    }

    #[test]
    fn batch_clear_keeps_capacity() {
        // given a filled batch
        let mut batch = batch_of(&[(1, &[0])]);
        batch.boundary = Some(block(1));
        let spans_capacity = batch.blocks.capacity();
        let events_capacity = batch.events.capacity();
        // when cleared
        batch.clear();
        // then empty with prior capacities
        assert!(batch.is_empty());
        assert_eq!(batch.boundary, None);
        assert_eq!(batch.spans().count(), 0);
        assert_eq!(batch.blocks.capacity(), spans_capacity);
        assert_eq!(batch.events.capacity(), events_capacity);
    }
}

#[cfg(verus_keep_ghost)]
verus! {

/// `v[k-1] < v[k]` for every `1 <= k < n`. Stated over pairs so the trigger does not
/// chain from `v[k]` to `v[k-1]`.
pub open spec fn ascending_upto<T: PartialOrd>(v: Seq<T>, n: int) -> bool {
    forall|j: int, k: int|
        #![trigger v[j], v[k]]
        0 <= j && k == j + 1 && k < n && k < v.len() ==> v[j].is_lt(&v[k])
}

/// `r` is what `first_descent(v)` returns: None when `v` ascends strictly, else the least
/// `i >= 1` with `v[i] <= v[i-1]` (T2).
pub open spec fn descent_result<T: PartialOrd>(v: Seq<T>, r: Option<usize>) -> bool {
    match r {
        None => ascending_upto(v, v.len() as int),
        Some(i) => 1 <= i < v.len() && v[i as int].is_le(&v[i - 1]) && ascending_upto(v, i as int),
    }
}

/// The iterator `events.into_iter()` returns follows vstd's iterator laws and has a
/// decreasing measure, so draining it terminates.
pub open spec fn finite_into_iter<I: IntoIterator>(events: I) -> bool {
    forall|it: I::IntoIter|
        #[trigger] call_ensures(I::into_iter, (events,), it) ==> it.obeys_prophetic_iter_laws()
            && it.decrease() is Some
}

/// `post` is `pre` with one span for `block` appended.
pub open spec fn pushed_block<E>(pre: BatchView<E>, post: BatchView<E>, block: BlockRef) -> bool {
    &&& post.wf()
    &&& post.blocks == pre.blocks.push(block.number)
    &&& post.hashes == pre.hashes.push(block.hash)
    &&& post.ends == pre.ends.push(post.events.len() as usize)
    &&& post.events.len() >= pre.events.len()
    &&& post.log_indices.subrange(0, pre.log_indices.len() as int) == pre.log_indices
    &&& post.events.subrange(0, pre.events.len() as int) == pre.events
}

/// `push_block_from_tail` popped the longest suffix of `before` whose entries are all in
/// `block`, and appended it in pop order (so a descending sort comes out ascending).
pub open spec fn popped_tail<E>(
    pre: BatchView<E>,
    post: BatchView<E>,
    before: Seq<(BlockRef, u32, E)>,
    after: Seq<(BlockRef, u32, E)>,
    block: BlockRef,
) -> bool {
    let n = before.len() - after.len();
    &&& after.len() <= before.len()
    &&& after == before.subrange(0, after.len() as int)
    &&& after.len() == 0 || after.last().0 != block
    &&& post.events.len() == pre.events.len() + n
    &&& appended_reversed(pre, post, before, n, block)
}

/// Entry `j` from the end of `before` is in `block` and is event `j` appended to `pre`.
pub open spec fn appended_at<E>(
    pre: BatchView<E>,
    post: BatchView<E>,
    before: Seq<(BlockRef, u32, E)>,
    j: int,
    block: BlockRef,
) -> bool {
    &&& before[before.len() - 1 - j].0 == block
    &&& post.log_indices[pre.log_indices.len() + j] == before[before.len() - 1 - j].1
    &&& post.events[pre.events.len() + j] == before[before.len() - 1 - j].2
}

/// The last `n` entries of `before`, last first, are events appended to `pre`.
pub open spec fn appended_reversed<E>(
    pre: BatchView<E>,
    post: BatchView<E>,
    before: Seq<(BlockRef, u32, E)>,
    n: int,
    block: BlockRef,
) -> bool {
    forall|j: int| 0 <= j < n ==> #[trigger] appended_at(pre, post, before, j, block)
}

/// Span `s` carries exactly span `i`'s positioned events.
pub open spec fn span_matches<'a, E>(b: BatchView<E>, i: int, s: SpanView<'a, E>) -> bool {
    &&& b.span_events(i).len() == s.events@.len()
    &&& s.log_indices@.len() == s.events@.len()
    &&& forall|k: int|
        #![trigger b.span_events(i)[k]]
        0 <= k < s.events@.len() ==> b.span_events(i)[k] == (
            Position { block: s.number, log_index: s.log_indices@[k] as u64 },
            s.events@[k],
        )
}

/// Span `i` is non-empty and its log indices ascend strictly.
pub open spec fn span_ok<E>(b: BatchView<E>, i: int) -> bool {
    &&& b.start(i) < b.ends[i]
    &&& forall|j: int, k: int|
        #![trigger b.log_indices[j], b.log_indices[k]]
        b.start(i) <= j < k < b.ends[i] ==> b.log_indices[j] < b.log_indices[k]
}

pub open spec fn spans_ok_upto<E>(b: BatchView<E>, n: int) -> bool {
    forall|i: int| 0 <= i < n ==> #[trigger] span_ok(b, i)
}

/// Each `validate` error names the first violation, checking blocks first and then
/// spans in order (T2).
pub open spec fn validate_names_first<E>(b: BatchView<E>, r: Result<(), BatchShapeError>) -> bool {
    match r {
        Ok(()) => true,
        Err(BatchShapeError::BlocksNotAscending { span }) => descent_result(b.blocks, Some(span)),
        Err(BatchShapeError::SpanEmpty { span }) => {
            &&& ascending_upto(b.blocks, b.blocks.len() as int)
            &&& span < b.ends.len()
            &&& spans_ok_upto(b, span as int)
            &&& b.ends[span as int] <= b.start(span as int)
        },
        Err(BatchShapeError::LogIndexNotAscending { span, index }) => {
            &&& ascending_upto(b.blocks, b.blocks.len() as int)
            &&& span < b.ends.len()
            &&& spans_ok_upto(b, span as int)
            &&& b.start(span as int) < b.ends[span as int]
            &&& b.start(span as int) <= index
            &&& descent_result(
                b.log_indices.subrange(b.start(span as int), b.ends[span as int] as int),
                Some((index - b.start(span as int)) as usize),
            )
        },
    }
}

/// For a lawful total order, `a <= b` is `!(b < a)`.
pub(crate) proof fn lemma_le_not_gt<T: Ord>(a: T, b: T)
    requires
        obeys_cmp::<T>(),
    ensures
        a.is_le(&b) <==> !b.is_lt(&a),
{
    reveal(vstd::laws_cmp::obeys_partial_cmp_spec_properties);
    reveal(vstd::laws_cmp::obeys_cmp_ord);
    assert(a.partial_cmp_spec(&b) == Some(a.cmp_spec(&b)));
}

proof fn lemma_ascending_from<T: Ord>(v: Seq<T>, i: int, j: int)
    requires
        obeys_cmp::<T>(),
        ascending_upto(v, v.len() as int),
        0 <= i < j < v.len(),
    ensures
        v[i].is_lt(&v[j]),
    decreases j - i,
{
    if j > i + 1 {
        lemma_ascending_from(v, i, j - 1);
        reveal(vstd::laws_cmp::obeys_partial_cmp_spec_properties);
        assert(v[j - 1].is_lt(&v[j]));
    }
}

/// Adjacent strict ascent is pairwise strict ascent.
pub(crate) proof fn lemma_ascending_pairwise<T: Ord>(v: Seq<T>)
    requires
        obeys_cmp::<T>(),
        ascending_upto(v, v.len() as int),
    ensures
        forall|i: int, j: int| #![trigger v[i], v[j]] 0 <= i < j < v.len() ==> v[i].is_lt(&v[j]),
{
    assert forall|i: int, j: int| #![trigger v[i], v[j]] 0 <= i < j < v.len() implies v[i].is_lt(&v[j]) by {
        lemma_ascending_from(v, i, j);
    }
}

proof fn lemma_int_laws()
    ensures
        obeys_cmp::<u64>(),
        obeys_cmp::<u32>(),
{
    broadcast use vstd::laws_cmp::group_laws_cmp;
}

/// Span `i` passed both `validate` checks.
proof fn lemma_span_passes<E>(b: BatchView<E>, i: int)
    requires
        b.wf(),
        0 <= i < b.ends.len(),
        b.start(i) < b.ends[i],
        ascending_upto(
            b.log_indices.subrange(b.start(i), b.ends[i] as int),
            b.ends[i] - b.start(i),
        ),
    ensures
        span_ok(b, i),
{
    lemma_int_laws();
    lemma_end_bounds(b, i);
    let lo = b.start(i);
    let sub = b.log_indices.subrange(lo, b.ends[i] as int);
    lemma_ascending_pairwise(sub);
    assert forall|j: int, k: int|
        #![trigger b.log_indices[j], b.log_indices[k]]
        lo <= j < k < b.ends[i] implies b.log_indices[j] < b.log_indices[k] by {
        assert(sub[j - lo] == b.log_indices[j]);
        assert(sub[k - lo] == b.log_indices[k]);
    }
}

/// A log index descent inside span `i` rules the batch out.
proof fn lemma_log_descent_unshaped<E>(b: BatchView<E>, i: int, offset: usize)
    requires
        b.wf(),
        0 <= i < b.ends.len(),
        b.start(i) < b.ends[i],
        descent_result(
            b.log_indices.subrange(b.start(i), b.ends[i] as int),
            Some(offset),
        ),
    ensures
        !b.shaped(),
{
    lemma_end_bounds(b, i);
    let lo = b.start(i);
    let sub = b.log_indices.subrange(lo, b.ends[i] as int);
    assert(sub[offset as int] == b.log_indices[lo + offset]);
    assert(sub[offset - 1] == b.log_indices[lo + offset - 1]);
    if b.shaped() {
        assert(b.log_indices[lo + offset - 1] < b.log_indices[lo + offset]);
    }
}

/// Span `i` lies inside the event lanes.
pub(crate) proof fn lemma_end_bounds<E>(b: BatchView<E>, i: int)
    requires
        b.wf(),
        0 <= i < b.ends.len(),
    ensures
        0 <= b.start(i) <= b.ends[i] <= b.events.len(),
        b.events.len() == b.log_indices.len(),
{
    let last = b.ends.len() - 1;
    if i < last {
        assert(b.ends[i] <= b.ends[last]);
    }
    if i > 0 {
        assert(b.ends[i - 1] <= b.ends[i]);
    }
}

proof fn lemma_spans_ok_shaped<E>(b: BatchView<E>)
    requires
        b.wf(),
        forall|i: int, j: int| #![trigger b.blocks[i], b.blocks[j]] 0 <= i < j < b.blocks.len() ==> b.blocks[i] < b.blocks[j],
        spans_ok_upto(b, b.ends.len() as int),
    ensures
        b.shaped(),
{
    assert forall|i: int| 0 <= i < b.ends.len() implies b.start(i) < #[trigger] b.ends[i] by {
        assert(span_ok(b, i));
    }
    assert forall|i: int, j: int, k: int|
        #![trigger b.ends[i], b.log_indices[j], b.log_indices[k]]
        0 <= i < b.ends.len() && b.start(i) <= j < k < b.ends[i]
        implies b.log_indices[j] < b.log_indices[k] by {
        assert(span_ok(b, i));
    }
}

/// Length of the first `n` spans flattened, and where each event lands in it.
pub(crate) proof fn lemma_flat_upto<E>(b: BatchView<E>, n: int)
    requires
        b.wf(),
        0 <= n <= b.ends.len(),
    ensures
        b.flat_upto(n).len() == b.start(n),
        forall|i: int, k: int|
            #![trigger b.flat_upto(n)[k], b.ends[i]]
            0 <= i < n && b.start(i) <= k < b.ends[i] ==> b.flat_upto(n)[k] == (
                Position { block: b.blocks[i], log_index: b.log_indices[k] as u64 },
                b.events[k],
            ),
    decreases n,
{
    if n > 0 {
        lemma_flat_upto(b, n - 1);
        lemma_end_bounds(b, n - 1);
        let prev = b.flat_upto(n - 1);
        let tail = b.span_events(n - 1);
        assert(b.flat_upto(n) == prev + tail);
        assert forall|i: int, k: int|
            #![trigger b.flat_upto(n)[k], b.ends[i]]
            0 <= i < n && b.start(i) <= k < b.ends[i] implies b.flat_upto(n)[k] == (
                Position { block: b.blocks[i], log_index: b.log_indices[k] as u64 },
                b.events[k],
            ) by {
            if i < n - 1 {
                lemma_end_bounds(b, i);
                if i < n - 2 {
                    assert(b.ends[i] <= b.ends[n - 2]);
                }
                assert(k < prev.len());
                assert(prev[k] == (
                    Position { block: b.blocks[i], log_index: b.log_indices[k] as u64 },
                    b.events[k],
                ));
            } else {
                assert(tail[k - b.start(n - 1)] == b.flat_upto(n)[k]);
            }
        }
    }
}

/// Every event index falls in some span.
pub(crate) proof fn lemma_span_of<E>(b: BatchView<E>, n: int, k: int) -> (i: int)
    requires
        b.wf(),
        0 <= n <= b.ends.len(),
        0 <= k < b.start(n),
    ensures
        0 <= i < n,
        b.start(i) <= k < b.ends[i],
    decreases n,
{
    if k >= b.start(n - 1) {
        n - 1
    } else {
        lemma_span_of(b, n - 1, k)
    }
}

/// T2: a shaped batch's flattened positions are strictly `lt`-ascending.
pub(crate) proof fn lemma_shaped_sorted<E>(b: BatchView<E>)
    requires
        b.wf(),
        b.shaped(),
    ensures
        lt_sorted(b.flat()),
{
    let n = b.ends.len() as int;
    let f = b.flat();
    lemma_flat_upto(b, n);
    assert forall|x: int, y: int| #![trigger f[x], f[y]] 0 <= x < y < f.len() implies lt(f[x].0, f[y].0) by {
        let i = lemma_span_of(b, n, x);
        let j = lemma_span_of(b, n, y);
        assert(f[x] == (Position { block: b.blocks[i], log_index: b.log_indices[x] as u64 }, b.events[x]));
        assert(f[y] == (Position { block: b.blocks[j], log_index: b.log_indices[y] as u64 }, b.events[y]));
        if j < i {
            if j < i - 1 {
                assert(b.ends[j] <= b.ends[i - 1]);
            }
        } else if i < j {
            assert(b.blocks[i] < b.blocks[j]);
        } else {
            assert(b.ends[i] > 0);
            assert(b.log_indices[x] < b.log_indices[y]);
        }
    }
}

/// Links `Batch@` to the fields, for verified code in other modules (which may read and
/// write `boundary` directly).
pub(crate) broadcast proof fn lemma_batch_view<E>(b: Batch<E>)
    ensures
        #[trigger] b@ == (BatchView {
            boundary: b.boundary,
            blocks: b.blocks@,
            hashes: b.hashes@,
            ends: b.ends@,
            log_indices: b.log_indices@,
            events: b.events@,
        }),
{
}

impl<'a, E> Spans<'a, E> {
    /// Holds between field writes in `next`, so it is a type invariant.
    #[verifier::type_invariant]
    spec fn inv(&self) -> bool {
        &&& self.batch@.wf()
        &&& self.next <= self.batch@.ends.len()
        &&& self.start <= self.batch@.events.len()
        &&& self.next < self.batch@.ends.len() ==> self.start <= self.batch@.ends[self.next as int]
    }
}

impl<E> View for Batch<E> {
    type V = BatchView<E>;

    closed spec fn view(&self) -> BatchView<E> {
        BatchView {
            boundary: self.boundary,
            blocks: self.blocks@,
            hashes: self.hashes@,
            ends: self.ends@,
            log_indices: self.log_indices@,
            events: self.events@,
        }
    }
}
} // verus!
