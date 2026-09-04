#![cfg(all(feature = "x25519", feature = "test-helpers"))]

use keystem::{
    InvalidKey,
    KemKeyOps,
    ViewingKey,
    ViewingPubkey,
    family::{
        Compliance,
        Incoming,
    },
    test_util::{
        conformance_generate_sk_draws,
        conformance_sk_codec_roundtrips,
        conformance_wrong_length_fails,
    },
};
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use sealring::{
    Domain,
    X25519,
    open,
    seal,
};

/// Seed for the x25519 conformance run.
const X25519_CONFORMANCE_SEED: u64 = 43;
/// Seed for the x25519 sk-bytes round trip.
const X25519_SK_ROUNDTRIP_SEED: u64 = 103;
/// Seed for the x25519 pubkey-bytes round trip.
const X25519_PUBKEY_ROUNDTRIP_SEED: u64 = 113;
/// Seed for the x25519 wrong-length rejection.
const X25519_WRONG_LENGTH_SEED: u64 = 153;
/// Seed for the family-separation check.
const FAMILY_SEPARATION_SEED: u64 = 211;
/// Seed for the seal/open interop check.
const SEAL_OPEN_SEED: u64 = 221;

#[test]
fn x25519_satisfies_the_kem_key_ops_conformance_suite() {
    // given a seeded generator and a fresh x25519 secret key drawn from it
    let mut rng = ChaCha20Rng::seed_from_u64(X25519_CONFORMANCE_SEED);
    let sk = X25519::generate_sk(&mut rng);
    // when the shared conformance probes run against it
    conformance_sk_codec_roundtrips::<X25519>(&sk);
    conformance_wrong_length_fails::<X25519>(&sk);
    conformance_generate_sk_draws::<X25519>(&mut rng);
    // then every codec, wrong-length, and draw-distinctness probe holds without panicking
}

#[test]
fn viewing_key_to_sk_bytes_then_from_sk_bytes_round_trips_for_x25519() {
    // given an x25519 viewing key drawn from a seeded generator
    let mut rng = ChaCha20Rng::seed_from_u64(X25519_SK_ROUNDTRIP_SEED);
    let original: ViewingKey<X25519, Incoming> = ViewingKey::random(&mut rng);
    let expected = original.derive_pubkey();
    // when its secret bytes are persisted through to_sk_bytes and reloaded through from_sk_bytes
    let sk_bytes = original.to_sk_bytes();
    let reloaded: ViewingKey<X25519, Incoming> =
        ViewingKey::from_sk_bytes(sk_bytes.as_ref())
            .expect("a freshly encoded sk decodes");
    // then the reloaded key derives the same viewing pubkey
    assert_eq!(reloaded.derive_pubkey(), expected);
}

#[test]
fn viewing_pubkey_to_bytes_then_from_bytes_round_trips_for_x25519() {
    // given an x25519 viewing pubkey derived from a freshly drawn viewing key
    let mut rng = ChaCha20Rng::seed_from_u64(X25519_PUBKEY_ROUNDTRIP_SEED);
    let key: ViewingKey<X25519, Incoming> = ViewingKey::random(&mut rng);
    let pubkey = key.derive_pubkey();
    // when its wire encoding is decoded back through from_bytes
    let decoded: ViewingPubkey<X25519, Incoming> =
        ViewingPubkey::from_bytes(pubkey.to_bytes().as_ref())
            .expect("its own encoding decodes");
    // then the recovered pubkey equals the original
    assert_eq!(decoded, pubkey);
}

#[test]
fn viewing_key_from_sk_bytes_rejects_a_wrong_length_string_for_x25519() {
    // given an x25519 secret-key encoding with one extra byte appended
    let mut rng = ChaCha20Rng::seed_from_u64(X25519_WRONG_LENGTH_SEED);
    let sk = X25519::generate_sk(&mut rng);
    let mut encoded = X25519::encode_sk(&sk).as_ref().to_vec();
    encoded.push(0);
    // when it is decoded as a viewing key
    let decoded = ViewingKey::<X25519, Incoming>::from_sk_bytes(&encoded);
    // then the wrong-length string is rejected
    assert_eq!(decoded.err(), Some(InvalidKey));
}

#[test]
fn incoming_and_compliance_viewing_keys_from_the_same_sk_bytes_derive_equal_wire_pubkeys()
{
    // given the same x25519 secret-key bytes handed to two different disclosure families
    let mut rng = ChaCha20Rng::seed_from_u64(FAMILY_SEPARATION_SEED);
    let sk_bytes = X25519::encode_sk(&X25519::generate_sk(&mut rng));
    let incoming: ViewingKey<X25519, Incoming> =
        ViewingKey::from_sk_bytes(&sk_bytes).expect("freshly generated sk bytes decode");
    let compliance: ViewingKey<X25519, Compliance> =
        ViewingKey::from_sk_bytes(&sk_bytes).expect("freshly generated sk bytes decode");
    // when both derive their viewing pubkeys and encode them to wire bytes
    let incoming_bytes = incoming.derive_pubkey().to_bytes();
    let compliance_bytes = compliance.derive_pubkey().to_bytes();
    // then the two families derive equal wire encodings, so the marker costs nothing on the wire
    assert_eq!(incoming_bytes.as_ref(), compliance_bytes.as_ref());
}

/// Note domain for the seal/open interop check: every byte string is a valid note.
struct KeystemTestDomain;

impl Domain for KeystemTestDomain {
    type Error = core::convert::Infallible;
    type Note = Vec<u8>;

    const DOMAIN_TAG: &'static str = "keystem-test/v1";

    fn encode_note(note: &Self::Note, out: &mut Vec<u8>) -> Result<(), Self::Error> {
        out.extend_from_slice(note);
        Ok(())
    }

    fn decode_note(bytes: &[u8]) -> Result<Self::Note, Self::Error> {
        Ok(bytes.to_vec())
    }
}

#[test]
fn sealing_a_note_to_an_x25519_viewing_pubkey_opens_with_the_matching_viewing_key() {
    // given an x25519 viewing key and a note a sender wants to deliver to it
    let mut rng = ChaCha20Rng::seed_from_u64(SEAL_OPEN_SEED);
    let viewing_key: ViewingKey<X25519, Incoming> = ViewingKey::random(&mut rng);
    let viewing_pubkey = viewing_key.derive_pubkey();
    let note = vec![9u8, 8, 7, 6];
    let aad = b"keystem-viewing-test-aad";
    // when the note is sealed to the pubkey and opened with the viewing key's own recipient
    let envelope = seal::<X25519, KeystemTestDomain>(
        viewing_pubkey.public_key(),
        &note,
        aad,
        &mut rng,
    )
    .expect("sealing to a valid pubkey succeeds");
    let opened =
        open::<X25519, KeystemTestDomain, _>(viewing_key.recipient(), &envelope, aad)
            .expect("opening with the matching recipient succeeds");
    // then the note comes back unchanged
    assert_eq!(opened, Some(note));
}

#[cfg(feature = "serde")]
mod viewing_pubkey_serde {
    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;
    use sealring::X25519;

    use super::{
        Incoming,
        ViewingKey,
        ViewingPubkey,
    };

    /// Seed for the x25519 serde round trip.
    const X25519_SERDE_SEED: u64 = 303;

    #[test]
    fn viewing_pubkey_round_trips_through_serde_json_for_x25519() {
        // given an x25519 viewing pubkey derived from a freshly drawn viewing key
        let mut rng = ChaCha20Rng::seed_from_u64(X25519_SERDE_SEED);
        let key: ViewingKey<X25519, Incoming> = ViewingKey::random(&mut rng);
        let pubkey = key.derive_pubkey();
        // when it is serialized to JSON and deserialized back
        let json = serde_json::to_string(&pubkey).expect("viewing pubkeys serialize");
        let decoded: ViewingPubkey<X25519, Incoming> =
            serde_json::from_str(&json).expect("its own JSON deserializes");
        // then the recovered pubkey equals the original
        assert_eq!(decoded, pubkey);
    }
}
