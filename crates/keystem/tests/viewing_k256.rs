#![cfg(all(feature = "k256", feature = "test-helpers"))]

use keystem::{
    InvalidKey,
    KemKeyOps,
    ViewingKey,
    ViewingPubkey,
    family::Incoming,
    test_util::{
        conformance_generate_sk_draws,
        conformance_sk_codec_roundtrips,
        conformance_wrong_length_fails,
    },
};
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use sealring::K256;

/// Seed for the k256 conformance run.
const K256_CONFORMANCE_SEED: u64 = 41;
/// Seed for the k256 sk-bytes round trip.
const K256_SK_ROUNDTRIP_SEED: u64 = 101;
/// Seed for the k256 pubkey-bytes round trip.
const K256_PUBKEY_ROUNDTRIP_SEED: u64 = 111;
/// Seed for the k256 wrong-length rejection.
const K256_WRONG_LENGTH_SEED: u64 = 151;
/// Seed for the Debug redaction check.
const DEBUG_SEED: u64 = 201;

#[test]
fn k256_satisfies_the_kem_key_ops_conformance_suite() {
    // given a seeded generator and a fresh secp256k1 secret key drawn from it
    let mut rng = ChaCha20Rng::seed_from_u64(K256_CONFORMANCE_SEED);
    let sk = K256::generate_sk(&mut rng);
    // when the shared conformance probes run against it
    conformance_sk_codec_roundtrips::<K256>(&sk);
    conformance_wrong_length_fails::<K256>(&sk);
    conformance_generate_sk_draws::<K256>(&mut rng);
    // then every codec, wrong-length, and draw-distinctness probe holds without panicking
}

#[test]
fn viewing_key_to_sk_bytes_then_from_sk_bytes_round_trips_for_k256() {
    // given a k256 viewing key drawn from a seeded generator
    let mut rng = ChaCha20Rng::seed_from_u64(K256_SK_ROUNDTRIP_SEED);
    let original: ViewingKey<K256, Incoming> = ViewingKey::random(&mut rng);
    let expected = original.derive_pubkey();
    // when its secret bytes are persisted through to_sk_bytes and reloaded through from_sk_bytes
    let sk_bytes = original.to_sk_bytes();
    let reloaded: ViewingKey<K256, Incoming> =
        ViewingKey::from_sk_bytes(sk_bytes.as_ref())
            .expect("a freshly encoded sk decodes");
    // then the reloaded key derives the same viewing pubkey
    assert_eq!(reloaded.derive_pubkey(), expected);
}

#[test]
fn viewing_pubkey_to_bytes_then_from_bytes_round_trips_for_k256() {
    // given a k256 viewing pubkey derived from a freshly drawn viewing key
    let mut rng = ChaCha20Rng::seed_from_u64(K256_PUBKEY_ROUNDTRIP_SEED);
    let key: ViewingKey<K256, Incoming> = ViewingKey::random(&mut rng);
    let pubkey = key.derive_pubkey();
    // when its wire encoding is decoded back through from_bytes
    let decoded: ViewingPubkey<K256, Incoming> =
        ViewingPubkey::from_bytes(pubkey.to_bytes().as_ref())
            .expect("its own encoding decodes");
    // then the recovered pubkey equals the original
    assert_eq!(decoded, pubkey);
}

#[test]
fn viewing_key_from_sk_bytes_rejects_a_wrong_length_string_for_k256() {
    // given a k256 secret-key encoding with one extra byte appended
    let mut rng = ChaCha20Rng::seed_from_u64(K256_WRONG_LENGTH_SEED);
    let sk = K256::generate_sk(&mut rng);
    let mut encoded = K256::encode_sk(&sk).as_ref().to_vec();
    encoded.push(0);
    // when it is decoded as a viewing key
    let decoded = ViewingKey::<K256, Incoming>::from_sk_bytes(&encoded);
    // then the wrong-length string is rejected
    assert_eq!(decoded.err(), Some(InvalidKey));
}

#[test]
fn viewing_key_debug_redacts_the_secret_key() {
    // given a k256 viewing key drawn from a seeded generator
    let mut rng = ChaCha20Rng::seed_from_u64(DEBUG_SEED);
    let key: ViewingKey<K256, Incoming> = ViewingKey::random(&mut rng);
    // when it is rendered with Debug
    let rendered = format!("{key:?}");
    // then it prints only the redaction marker
    assert_eq!(rendered, "ViewingKey(REDACTED)");
}

#[cfg(feature = "serde")]
mod viewing_pubkey_serde {
    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;
    use sealring::K256;

    use super::{
        Incoming,
        ViewingKey,
        ViewingPubkey,
    };

    /// Seed for the k256 serde round trip.
    const K256_SERDE_SEED: u64 = 301;

    #[test]
    fn viewing_pubkey_round_trips_through_serde_json_for_k256() {
        // given a k256 viewing pubkey derived from a freshly drawn viewing key
        let mut rng = ChaCha20Rng::seed_from_u64(K256_SERDE_SEED);
        let key: ViewingKey<K256, Incoming> = ViewingKey::random(&mut rng);
        let pubkey = key.derive_pubkey();
        // when it is serialized to JSON and deserialized back
        let json = serde_json::to_string(&pubkey).expect("viewing pubkeys serialize");
        let decoded: ViewingPubkey<K256, Incoming> =
            serde_json::from_str(&json).expect("its own JSON deserializes");
        // then the recovered pubkey equals the original
        assert_eq!(decoded, pubkey);
    }
}
