#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::verus::model::opt_lt;

/// Total order over chain events: block number, then log index within the block.
#[cfg_attr(verus_keep_ghost, verus_verify, derive(StructuralEq))]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Position {
    /// Block number the event belongs to.
    pub block: u64,
    /// Index of the log within its block.
    pub log_index: u64,
}

#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl Position {
    /// Builds a position from a block number and its log index.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == (Position { block, log_index })))]
    pub const fn new(block: u64, log_index: u64) -> Self {
        Self { block, log_index }
    }
}

/// True when `a` is strictly after `b` in the position order, with None before every
/// position. Spelled out rather than derived so the verifier can state it.
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == opt_lt(b, a)))]
pub(crate) fn pos_gt(a: Option<Position>, b: Option<Position>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => {
            a.block > b.block || (a.block == b.block && a.log_index > b.log_index)
        }
        (Some(_), None) => true,
        (None, _) => false,
    }
}

/// A block identified by number and hash; the hash commits to the full ancestry.
#[cfg_attr(verus_keep_ghost, verus_verify, derive(StructuralEq))]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BlockRef {
    /// Block number.
    pub number: u64,
    /// Block hash, committing to the full ancestry.
    pub hash: [u8; 32],
}

#[cfg(test)]
mod tests {
    use super::{
        Position,
        pos_gt,
    };

    #[test]
    fn position_order_is_block_then_log_index() {
        // given positions across two blocks with mixed log indices
        let mut positions = [
            Position::new(2, 0),
            Position::new(1, 5),
            Position::new(1, 1),
            Position::new(2, 3),
        ];
        // when sorted
        positions.sort();
        // then block dominates and log_index breaks ties within a block
        assert_eq!(
            positions,
            [
                Position::new(1, 1),
                Position::new(1, 5),
                Position::new(2, 0),
                Position::new(2, 3),
            ]
        );
    }

    #[test]
    fn pos_gt_agrees_with_the_derived_option_order() {
        // given positions around one block, plus None
        let points = [
            None,
            Some(Position::new(1, 0)),
            Some(Position::new(1, 1)),
            Some(Position::new(2, 0)),
        ];
        // when every ordered pair is compared
        // then pos_gt matches Option's derived order, which puts None first
        for a in points {
            for b in points {
                assert_eq!(pos_gt(a, b), a > b, "{a:?} vs {b:?}");
            }
        }
    }
}
