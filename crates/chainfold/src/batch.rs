#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use core::fmt;

use crate::position::BlockRef;

/// One event with its log index; the block number lives on the owning span.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LogEvent<E> {
    /// Index of the log within its block.
    pub log_index: u64,
    /// Consumer event decoded from the log.
    pub event: E,
}

/// Half-open range of events belonging to one observed block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BlockSpan {
    /// Block the events belong to.
    pub block: BlockRef,
    /// First event index in the batch's event array.
    pub start: u32,
    /// One past the last event index in the batch's event array.
    pub end: u32,
}

/// One poll's worth of events in flat layout, reusable across polls.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Batch<E> {
    /// Refetched header of the cursor block; None means the source could not produce it.
    pub boundary: Option<BlockRef>,
    /// One span per observed block, ascending, each covering a contiguous event range.
    pub spans: Vec<BlockSpan>,
    /// Every event of the batch, ordered by block then log index.
    pub events: Vec<LogEvent<E>>,
}

impl<E> Batch<E> {
    /// Builds an empty, capacity-free batch.
    pub fn new() -> Self {
        Self {
            boundary: None,
            spans: Vec::new(),
            events: Vec::new(),
        }
    }

    /// Empties spans, events, and boundary while keeping capacity.
    pub fn clear(&mut self) {
        self.boundary = None;
        self.spans.clear();
        self.events.clear();
    }

    /// True when the batch carries no spans.
    pub fn is_empty(&self) -> bool {
        self.spans.is_empty()
    }

    /// Validates the flat batch shape against the rules of record.
    pub fn validate(&self) -> Result<(), BatchShapeError> {
        if u32::try_from(self.events.len()).is_err() {
            return Err(BatchShapeError::TooManyEvents {
                len: self.events.len(),
            });
        }
        let mut previous: Option<&BlockSpan> = None;
        for (span_index, span) in self.spans.iter().enumerate() {
            if span.start >= span.end || span.end as usize > self.events.len() {
                return Err(BatchShapeError::SpanBoundsInvalid { span: span_index });
            }
            if span.start != previous.map_or(0, |previous| previous.end) {
                return Err(BatchShapeError::SpansNotContiguous { span: span_index });
            }
            if previous.is_some_and(|previous| span.block.number <= previous.block.number)
            {
                return Err(BatchShapeError::BlocksNotAscending { span: span_index });
            }
            let events = &self.events[span.start as usize..span.end as usize];
            let ascending = events
                .iter()
                .zip(&events[1..])
                .fold(true, |acc, (a, b)| acc & (a.log_index < b.log_index));
            if !ascending {
                let offset = events
                    .windows(2)
                    .position(|pair| pair[1].log_index <= pair[0].log_index)
                    .expect("a failed ascending sweep always has a locatable pair");
                return Err(BatchShapeError::LogIndexNotAscending {
                    span: span_index,
                    index: span.start + 1 + offset as u32,
                });
            }
            previous = Some(span);
        }
        if previous.map_or(0, |span| span.end) as usize != self.events.len() {
            return Err(BatchShapeError::SpansNotContiguous {
                span: self.spans.len().saturating_sub(1),
            });
        }
        Ok(())
    }
}

impl<E> Default for Batch<E> {
    fn default() -> Self {
        Self::new()
    }
}

/// Batch layout violation found before any event reaches the fold.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BatchShapeError {
    /// Batch carries more events than an index can address.
    TooManyEvents {
        /// Events the batch carries.
        len: usize,
    },
    /// Span is empty or reaches past the event array.
    SpanBoundsInvalid {
        /// Index of the offending span.
        span: usize,
    },
    /// Span does not start where its predecessor ended.
    SpansNotContiguous {
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
        /// Index of the offending event in the batch's event array.
        index: u32,
    },
}

impl fmt::Display for BatchShapeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooManyEvents { len } => {
                write!(f, "batch carries {len} events, exceeding u32::MAX")
            }
            Self::SpanBoundsInvalid { span } => {
                write!(f, "span {span} is empty or has out-of-range bounds")
            }
            Self::SpansNotContiguous { span } => {
                write!(f, "span {span} is not contiguous with its neighbor")
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
        BlockSpan,
    };
    use crate::position::BlockRef;
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
        BlockRef {
            number,
            hash: [0; 32],
        }
    }

    fn events(indices: &[u64]) -> Vec<super::LogEvent<u64>> {
        indices
            .iter()
            .map(|&log_index| super::LogEvent {
                log_index,
                event: log_index,
            })
            .collect()
    }

    #[test]
    fn valid_batch_passes_validation() {
        // given two spans covering four events contiguously
        let batch = Batch {
            boundary: None,
            spans: vec![
                BlockSpan {
                    block: block(1),
                    start: 0,
                    end: 2,
                },
                BlockSpan {
                    block: block(2),
                    start: 2,
                    end: 4,
                },
            ],
            events: events(&[0, 1, 0, 1]),
        };
        // when validated
        let result = batch.validate();
        // then Ok
        assert_eq!(result, Ok(()));
    }

    #[test]
    fn batch_with_gap_between_spans_fails() {
        // given span end 2 and next start 3
        let batch = Batch {
            boundary: None,
            spans: vec![
                BlockSpan {
                    block: block(1),
                    start: 0,
                    end: 2,
                },
                BlockSpan {
                    block: block(2),
                    start: 3,
                    end: 4,
                },
            ],
            events: events(&[0, 1, 0, 1]),
        };
        // when validated
        let result = batch.validate();
        // then SpansNotContiguous at span 1
        assert_eq!(result, Err(BatchShapeError::SpansNotContiguous { span: 1 }));
    }

    #[test]
    fn batch_with_descending_blocks_fails() {
        // given spans at blocks 7 then 5
        let batch = Batch {
            boundary: None,
            spans: vec![
                BlockSpan {
                    block: block(7),
                    start: 0,
                    end: 1,
                },
                BlockSpan {
                    block: block(5),
                    start: 1,
                    end: 2,
                },
            ],
            events: events(&[0, 0]),
        };
        // when validated
        let result = batch.validate();
        // then BlocksNotAscending at span 1
        assert_eq!(result, Err(BatchShapeError::BlocksNotAscending { span: 1 }));
    }

    #[test]
    fn batch_with_repeated_log_index_fails() {
        // given one span with log indices 3, 3
        let batch = Batch {
            boundary: None,
            spans: vec![BlockSpan {
                block: block(1),
                start: 0,
                end: 2,
            }],
            events: events(&[3, 3]),
        };
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
        // given a second span whose start equals its end
        let batch = Batch {
            boundary: None,
            spans: vec![
                BlockSpan {
                    block: block(1),
                    start: 0,
                    end: 1,
                },
                BlockSpan {
                    block: block(2),
                    start: 1,
                    end: 1,
                },
            ],
            events: events(&[0]),
        };
        // when validated
        let result = batch.validate();
        // then SpanBoundsInvalid at span 1
        assert_eq!(result, Err(BatchShapeError::SpanBoundsInvalid { span: 1 }));
    }

    #[test]
    fn batch_with_events_but_no_spans_fails() {
        // given one event and zero spans
        let batch = Batch {
            boundary: None,
            spans: vec![],
            events: events(&[0]),
        };
        // when validated
        let result = batch.validate();
        // then SpansNotContiguous at span 0
        assert_eq!(result, Err(BatchShapeError::SpansNotContiguous { span: 0 }));
    }

    #[test]
    fn batch_clear_keeps_capacity() {
        // given a filled batch
        let mut batch = Batch {
            boundary: Some(block(1)),
            spans: vec![BlockSpan {
                block: block(1),
                start: 0,
                end: 1,
            }],
            events: events(&[0]),
        };
        let spans_capacity = batch.spans.capacity();
        let events_capacity = batch.events.capacity();
        // when cleared
        batch.clear();
        // then empty with prior capacities
        assert!(batch.is_empty());
        assert_eq!(batch.boundary, None);
        assert!(batch.events.is_empty());
        assert_eq!(batch.spans.capacity(), spans_capacity);
        assert_eq!(batch.events.capacity(), events_capacity);
    }
}
