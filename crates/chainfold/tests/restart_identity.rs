#![cfg(feature = "wincode")]
//! Property test: restart from a mid-run snapshot reproduces byte-identical state.

use chainfold::{
    Batch,
    BlockRef,
    Engine,
    EngineConfig,
    test_util::RecordingFold,
};
use proptest::prelude::*;

/// Ring window small enough that a 40-block schedule wraps at least once.
const RING_CAPACITY: usize = 8;

fn test_config() -> EngineConfig {
    EngineConfig {
        ring_capacity: RING_CAPACITY,
        checkpoint_slots: 0,
    }
}

/// Deterministic block header: the block number embedded directly in the hash bytes.
fn block_ref(number: u64) -> BlockRef {
    let mut hash = [0u8; 32];
    hash[..8].copy_from_slice(&number.to_le_bytes());
    BlockRef { number, hash }
}

/// Applies one block; a zero-event block is left out, as a source spans whole blocks
/// that carry events.
fn apply_block(engine: &mut Engine<RecordingFold>, number: u64, event_count: usize) {
    if event_count == 0 {
        return;
    }
    let boundary = engine.cursor().map(|cursor| block_ref(cursor.block));
    let mut batch = Batch::new();
    batch.boundary = boundary;
    batch.push_block(
        block_ref(number),
        (0..event_count as u32).map(|log_index| (log_index, u64::from(log_index))),
    );
    engine.apply_batch(&batch).unwrap();
}

/// A block schedule of 1..=40 event counts (0..=4 each) plus a valid split index.
fn schedule_and_split() -> impl Strategy<Value = (Vec<usize>, usize)> {
    prop::collection::vec(0usize..=4, 1..=40).prop_flat_map(|schedule| {
        let len = schedule.len();
        (Just(schedule), 0..=len)
    })
}

proptest! {
    #[test]
    fn restart_reproduces_byte_identical_state((schedule, split) in schedule_and_split()) {
        // given engine A applying blocks 0..split then encoding
        let mut engine_a = Engine::new(RecordingFold::default(), test_config()).unwrap();
        for (index, &count) in schedule[..split].iter().enumerate() {
            apply_block(&mut engine_a, index as u64 + 1, count);
        }
        let mut snapshot = Vec::new();
        engine_a.encode_snapshot(&mut snapshot).unwrap();

        // when engine B decodes and both apply blocks split.. (ring wraps at capacity 8)
        let mut engine_b =
            Engine::<RecordingFold>::decode_snapshot(&snapshot, test_config()).unwrap();
        for (index, &count) in schedule[split..].iter().enumerate() {
            let number = (split + index) as u64 + 1;
            apply_block(&mut engine_a, number, count);
            apply_block(&mut engine_b, number, count);
        }

        // then encode_snapshot of A and B are byte-identical, including ring wrap
        let mut bytes_a = Vec::new();
        let mut bytes_b = Vec::new();
        engine_a.encode_snapshot(&mut bytes_a).unwrap();
        engine_b.encode_snapshot(&mut bytes_b).unwrap();
        prop_assert_eq!(bytes_a, bytes_b);
    }
}
