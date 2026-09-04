use std::{
    collections::HashSet,
    hint::black_box,
};

use criterion::{
    BenchmarkGroup,
    Criterion,
    Throughput,
    criterion_group,
    criterion_main,
    measurement::WallTime,
};
use keystem::curves::bn254::{
    OwnerPubkey,
    SpendingKey,
};
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;

/// Seed for the rng behind the one fixed key most benchmarks derive from.
const FIXED_KEY_SEED: u64 = 0x5eed_5eed_5eed_5eed;

/// Seed for the rng hoisted into the `random` benchmark's timed loop.
const RANDOM_SEED: u64 = 0x1234_5678_9abc_def0;

/// Seed for the rng that draws the distinct keys in the batch benchmark.
const BATCH_SEED: u64 = 0x8888_7777_6666_5555;

/// Keys derived in one timed iteration of the batch benchmark, enough to
/// carry the thread-local hasher past its one-time construction so the
/// steady-state per-derivation cost sits next to the single-shot number.
const DERIVATIONS_PER_BATCH: usize = 64;

/// All-ones encoding. BN254's scalar field is 254 bits wide, so this string
/// sits above the modulus and the reduce-and-compare check always rejects it.
const REJECTED_ENCODING: [u8; 32] = [0xffu8; 32];

type SpendGroup<'a> = BenchmarkGroup<'a, WallTime>;

/// The Poseidon1 permutation, the dominant cost on this side of the crate.
fn bench_derivation(group: &mut SpendGroup<'_>, key: &SpendingKey) {
    assert_ne!(key.derive_owner_pubkey().to_bytes(), [0u8; 32]);

    group.bench_function("derive_owner_pubkey", |b| {
        b.iter(|| black_box(black_box(key).derive_owner_pubkey()));
    });
}

/// Rejection sampling, one draw per iteration.
fn bench_generation(group: &mut SpendGroup<'_>) {
    let mut rng = ChaCha20Rng::seed_from_u64(RANDOM_SEED);

    let _ = black_box(SpendingKey::random(&mut rng));

    group.bench_function("random", |b| {
        b.iter(|| black_box(SpendingKey::random(&mut rng)));
    });
}

/// The checked import path, on both the accepted and the rejected encoding.
/// A consumer validating untrusted counterparty keys pays the reject side.
fn bench_decode(group: &mut SpendGroup<'_>, key: &SpendingKey) {
    let accepted = *key.scalar().expose_bytes();
    assert!(SpendingKey::from_canonical_bytes(accepted).is_ok());
    assert!(SpendingKey::from_canonical_bytes(REJECTED_ENCODING).is_err());

    group.bench_function("from_canonical_bytes_accept", |b| {
        b.iter(|| black_box(SpendingKey::from_canonical_bytes(black_box(accepted))));
    });

    group.bench_function("from_canonical_bytes_reject", |b| {
        b.iter(|| {
            black_box(SpendingKey::from_canonical_bytes(black_box(
                REJECTED_ENCODING,
            )))
        });
    });
}

fn bench_field_utils(group: &mut SpendGroup<'_>, key: &SpendingKey) {
    let pubkey = key.derive_owner_pubkey();
    let value = pubkey.to_field();

    group.bench_function("owner_pubkey_to_field", |b| {
        b.iter(|| black_box(black_box(&pubkey).to_field()));
    });

    group.bench_function("owner_pubkey_from_field", |b| {
        b.iter(|| black_box(OwnerPubkey::from_field(black_box(value))));
    });

    group.bench_function("scalar", |b| {
        b.iter(|| black_box(black_box(key).scalar()));
    });
}

fn bench_derivation_batch(group: &mut SpendGroup<'_>) {
    let mut rng = ChaCha20Rng::seed_from_u64(BATCH_SEED);
    let keys: Vec<SpendingKey> = (0..DERIVATIONS_PER_BATCH)
        .map(|_| SpendingKey::random(&mut rng))
        .collect();

    let distinct: HashSet<[u8; 32]> = keys
        .iter()
        .map(|key| key.derive_owner_pubkey().to_bytes())
        .collect();
    assert_eq!(
        distinct.len(),
        DERIVATIONS_PER_BATCH,
        "batch keys must derive distinct owner pubkeys"
    );

    group.throughput(Throughput::Elements(DERIVATIONS_PER_BATCH as u64));
    group.bench_function("derive_owner_pubkey_batch", |b| {
        b.iter(|| {
            for key in &keys {
                black_box(black_box(key).derive_owner_pubkey());
            }
        });
    });
}

fn bench_spend(c: &mut Criterion) {
    let mut group = c.benchmark_group("keystem::spend");
    let key = SpendingKey::random(&mut ChaCha20Rng::seed_from_u64(FIXED_KEY_SEED));

    bench_derivation(&mut group, &key);
    bench_generation(&mut group);
    bench_decode(&mut group, &key);
    bench_field_utils(&mut group, &key);
    bench_derivation_batch(&mut group);

    group.finish();
}

criterion_group!(benches, bench_spend);
criterion_main!(benches);
