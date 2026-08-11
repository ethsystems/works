//! Snapshot envelope codec cost: encode and decode over a fixed-size recorded state.

use std::hint::black_box;

use chainfold::{
    Batch,
    BlockRef,
    Engine,
    EngineConfig,
    test_util::RecordingFold,
};
use criterion::{
    Criterion,
    Throughput,
    criterion_group,
    criterion_main,
};

/// Observed-block ring window; only one block is ever observed in this benchmark.
const RING_CAPACITY: usize = 8;
/// Recorded-fold entries the envelope carries.
const ENTRY_COUNT: u32 = 4096;

/// Builds a distinguishable header for a block number.
fn block_ref(number: u64) -> BlockRef {
    let mut hash = [0u8; 32];
    hash[..8].copy_from_slice(&number.to_le_bytes());
    BlockRef { number, hash }
}

/// Builds an engine whose fold carries `ENTRY_COUNT` recorded entries.
fn recorded_engine() -> Engine<RecordingFold> {
    let config = EngineConfig {
        ring_capacity: RING_CAPACITY,
        checkpoint_slots: 0,
    };
    let mut engine =
        Engine::new(RecordingFold::default(), config).expect("engine config is valid");
    let mut batch = Batch::new();
    batch.push_block(
        block_ref(1),
        (0..ENTRY_COUNT).map(|log_index| (log_index, u64::from(log_index))),
    );
    engine.apply_batch(&batch).expect("apply_batch succeeds");
    engine
}

fn bench_snapshot_encode(c: &mut Criterion) {
    let engine = recorded_engine();
    let mut out = Vec::new();
    engine.encode_snapshot(&mut out).expect("encode succeeds");
    let mut group = c.benchmark_group("chainfold::snapshot_encode");
    group.throughput(Throughput::Bytes(out.len() as u64));
    group.bench_function(format!("n={ENTRY_COUNT}"), |b| {
        b.iter(|| {
            out.clear();
            engine
                .encode_snapshot(black_box(&mut out))
                .expect("encode succeeds");
        });
    });
    group.finish();
}

fn bench_snapshot_decode(c: &mut Criterion) {
    let engine = recorded_engine();
    let config = EngineConfig {
        ring_capacity: RING_CAPACITY,
        checkpoint_slots: 0,
    };
    let mut bytes = Vec::new();
    engine.encode_snapshot(&mut bytes).unwrap();
    let mut group = c.benchmark_group("chainfold::snapshot_decode");
    group.throughput(Throughput::Bytes(bytes.len() as u64));
    group.bench_function(format!("n={ENTRY_COUNT}"), |b| {
        b.iter(|| {
            let decoded =
                Engine::<RecordingFold>::decode_snapshot(black_box(&bytes), config)
                    .expect("decode succeeds");
            black_box(decoded);
        });
    });
    group.finish();
}

criterion_group!(benches, bench_snapshot_encode, bench_snapshot_decode);
criterion_main!(benches);
