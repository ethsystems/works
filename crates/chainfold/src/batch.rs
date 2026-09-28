#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use core::fmt;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use crate::position::BlockRef;
#[cfg(verus_keep_ghost)]
use crate::verus::model::BatchView;

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
    blocks: Vec<u64>,
    hashes: Vec<[u8; 32]>,
    ends: Vec<usize>,
    log_indices: Vec<u32>,
    events: Vec<E>,
}

impl<E> Batch<E> {
    /// Builds an empty, capacity-free batch.
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
    pub fn clear(&mut self) {
        self.boundary = None;
        self.blocks.clear();
        self.hashes.clear();
        self.ends.clear();
        self.log_indices.clear();
        self.events.clear();
    }

    /// True when the batch carries no spans.
    pub fn is_empty(&self) -> bool {
        self.ends.is_empty()
    }

    /// Spans the batch carries, one per observed block.
    pub fn span_count(&self) -> usize {
        self.ends.len()
    }

    /// Appends one block's complete event set in log order.
    pub fn push_block(
        &mut self,
        block: BlockRef,
        events: impl IntoIterator<Item = (u32, E)>,
    ) {
        self.blocks.push(block.number);
        self.hashes.push(block.hash);
        let mut events = events.into_iter();
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
    pub fn spans(&self) -> Spans<'_, E> {
        Spans {
            batch: self,
            next: 0,
            start: 0,
        }
    }

    /// Validates the orderings a source controls, before any event reaches the fold.
    pub fn validate(&self) -> Result<(), BatchShapeError> {
        if let Some(span) = first_descent(&self.blocks) {
            return Err(BatchShapeError::BlocksNotAscending { span });
        }
        let mut start = 0usize;
        for span in 0..self.ends.len() {
            let end = self.ends[span];
            if end <= start {
                return Err(BatchShapeError::SpanEmpty { span });
            }
            if let Some(offset) = first_descent(&self.log_indices[start..end]) {
                return Err(BatchShapeError::LogIndexNotAscending {
                    span,
                    index: start + offset,
                });
            }
            start = end;
        }
        Ok(())
    }
}

/// Index of the first element that does not exceed its predecessor.
///
/// The sweep is branchless so it vectorizes; the cold locate pass runs only on failure.
pub(crate) fn first_descent<T: Ord>(values: &[T]) -> Option<usize> {
    let mut ascending = true;
    for i in 1..values.len() {
        ascending &= values[i - 1] < values[i];
    }
    if ascending {
        return None;
    }
    locate_descent(values)
}

#[cold]
#[expect(clippy::manual_find, reason = "Verus has no spec for Iterator::find")]
fn locate_descent<T: Ord>(values: &[T]) -> Option<usize> {
    for i in 1..values.len() {
        if values[i] <= values[i - 1] {
            return Some(i);
        }
    }
    None
}

/// Oldest-first iterator over a batch's spans.
#[derive(Debug)]
pub struct Spans<'a, E> {
    batch: &'a Batch<E>,
    next: usize,
    start: usize,
}

impl<'a, E> Iterator for Spans<'a, E> {
    type Item = SpanView<'a, E>;

    fn next(&mut self) -> Option<Self::Item> {
        let end = *self.batch.ends.get(self.next)?;
        let range = self.start..end;
        let number = self.batch.blocks[self.next];
        let hash = &self.batch.hashes[self.next];
        self.next += 1;
        self.start = end;
        Some(SpanView {
            number,
            hash,
            log_indices: &self.batch.log_indices[range.clone()],
            events: &self.batch.events[range],
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.batch.ends.len() - self.next;
        (remaining, Some(remaining))
    }
}

impl<E> ExactSizeIterator for Spans<'_, E> {}

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
impl<E> View for Batch<E> {
    type V = BatchView<E>;

    closed spec fn view(&self) -> BatchView<E> {
        BatchView {
            blocks: self.blocks@,
            hashes: self.hashes@,
            ends: self.ends@,
            log_indices: self.log_indices@,
            events: self.events@,
        }
    }
}
} // verus!
