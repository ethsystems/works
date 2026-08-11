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

use core::cmp::Ordering;

use crate::position::BlockRef;

/// Bounded history of observed blocks, structure of arrays, power-of-two capacity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BlockRing {
    numbers: Box<[u64]>,
    hashes: Box<[[u8; 32]]>,
    head: usize,
    len: usize,
}

impl BlockRing {
    /// Capacity must be a power of two; enforced by EngineConfig validation.
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        debug_assert!(
            capacity.is_power_of_two(),
            "BlockRing capacity must be a power of two"
        );
        Self {
            numbers: vec![0u64; capacity].into_boxed_slice(),
            hashes: vec![[0u8; 32]; capacity].into_boxed_slice(),
            head: 0,
            len: 0,
        }
    }

    #[inline]
    pub(crate) fn capacity(&self) -> usize {
        self.numbers.len()
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    fn physical(&self, logical: usize) -> usize {
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

    #[inline]
    pub(crate) fn newest(&self) -> Option<BlockRef> {
        if self.is_empty() {
            None
        } else {
            Some(self.get(self.len - 1))
        }
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
        let mut low = 0usize;
        let mut high = self.len;
        while low < high {
            let mid = low + (high - low) / 2;
            let physical = self.physical(mid);
            match self.numbers[physical].cmp(&number) {
                Ordering::Less => low = mid + 1,
                Ordering::Equal => return Some(self.hashes[physical]),
                Ordering::Greater => high = mid,
            }
        }
        None
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

impl<'a> ExactSizeIterator for Observed<'a> {
    fn len(&self) -> usize {
        self.remaining
    }
}

#[cfg(test)]
mod tests {
    use super::BlockRing;
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
        let newest = ring.newest();
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
    fn clone_is_independent() {
        // given a cloned ring
        let mut ring = BlockRing::with_capacity(4);
        ring.push(block(1));
        let clone = ring.clone();
        // when pushing to the original
        ring.push(block(2));
        // then the clone is unchanged
        assert_eq!(clone.newest(), Some(block(1)));
        assert_eq!(ring.newest(), Some(block(2)));
    }
}
