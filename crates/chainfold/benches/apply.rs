//! Engine apply-path overhead: pure bookkeeping cost isolated behind a no-op fold.

use std::hint::black_box;

use chainfold::{
    Batch,
    BlockRef,
    Engine,
    EngineConfig,
    test_util::NoopFold,
};
use criterion::{
    BatchSize,
    Criterion,
    Throughput,
    criterion_group,
    criterion_main,
};

/// Observed-block ring window, sized past the warmup block plus every timed span.
const RING_CAPACITY: usize = 128;
/// Blocks the timed batch spans.
const SPAN_COUNT: u64 = 64;
/// Events carried by each timed span.
const EVENTS_PER_SPAN: u32 = 64;
/// Total events the timed batch carries.
const EVENT_COUNT: u64 = SPAN_COUNT * EVENTS_PER_SPAN as u64;

/// Builds a distinguishable header for a block number.
fn block_ref(number: u64) -> BlockRef {
    let mut hash = [0u8; 32];
    hash[..8].copy_from_slice(&number.to_le_bytes());
    BlockRef { number, hash }
}

/// Builds a fresh engine and applies one warmup block, so the timed batch carries a
/// boundary that matches the ring's newest entry.
fn warmed_engine() -> Engine<NoopFold> {
    let config = EngineConfig {
        ring_capacity: RING_CAPACITY,
        checkpoint_slots: 0,
    };
    let mut engine = Engine::new(NoopFold, config).expect("engine config is valid");
    let mut warmup = Batch::new();
    warmup.push_block(block_ref(0), [(0u32, 0u64)]);
    engine
        .apply_batch(&warmup)
        .expect("warmup batch applies cleanly");
    engine
}

/// Builds the batch under measurement: 4096 events over 64 spans past the warmup block.
fn timed_batch() -> Batch<u64> {
    let mut batch = Batch::new();
    batch.boundary = Some(block_ref(0));
    for block in 1..=SPAN_COUNT {
        batch.push_block(
            block_ref(block),
            (0..EVENTS_PER_SPAN).map(|log_index| (log_index, u64::from(log_index))),
        );
    }
    batch
}

fn bench_apply(c: &mut Criterion) {
    let batch = timed_batch();
    let mut group = c.benchmark_group("chainfold::apply");
    group.throughput(Throughput::Elements(EVENT_COUNT));
    group.bench_function(format!("fold=noop n={EVENT_COUNT}"), |b| {
        b.iter_batched(
            warmed_engine,
            |mut engine| {
                engine
                    .apply_batch(black_box(&batch))
                    .expect("apply_batch succeeds");
            },
            BatchSize::SmallInput,
        );
    });
    group.finish();
}

criterion_group!(benches, bench_apply);
criterion_main!(benches);
