#![cfg(feature = "poseidon")]

use std::collections::HashSet;

use ark_ff::{
    BigInteger,
    PrimeField,
};
use keystem::{
    SpendAuthority,
    curves::bn254::{
        Fr,
        OwnerPubkey,
        SecretScalar,
        SpendingKey,
    },
};
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use zeroize::ZeroizeOnDrop;

/// Seed for every generator drawn in this file, replayed on failure.
const SEED: u64 = 0xC0FFEE;

/// Lowercase hex encoding of `bytes`, matching the crate's own `Debug` output.
fn hex_of(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// The canonical big-endian encoding of BN254's largest scalar, modulus minus one.
fn modulus_minus_one_bytes() -> [u8; 32] {
    OwnerPubkey::from_field(-Fr::from(1u64)).to_bytes()
}

/// The big-endian encoding of BN254's scalar field modulus itself.
fn modulus_bytes() -> [u8; 32] {
    Fr::MODULUS
        .to_bytes_be()
        .try_into()
        .expect("BN254's scalar modulus is 32 bytes wide")
}

#[test]
fn spending_key_from_canonical_bytes_accepts_the_modulus_minus_one() {
    // given the canonical encoding of BN254's largest scalar
    let bytes = modulus_minus_one_bytes();
    // when it is decoded as a spending key
    let decoded = SpendingKey::from_canonical_bytes(bytes);
    // then it is accepted
    assert!(decoded.is_ok());
}

#[test]
fn spending_key_from_canonical_bytes_rejects_the_modulus() {
    // given the big-endian encoding of the scalar field modulus
    let bytes = modulus_bytes();
    // when it is decoded as a spending key
    let decoded = SpendingKey::from_canonical_bytes(bytes);
    // then the reduce-and-compare check rejects it
    assert!(decoded.is_err());
}

#[test]
fn spending_key_from_canonical_bytes_rejects_an_all_ones_string() {
    // given a byte string far above the modulus
    let bytes = [0xffu8; 32];
    // when it is decoded as a spending key
    let decoded = SpendingKey::from_canonical_bytes(bytes);
    // then it is rejected rather than silently reduced
    assert!(decoded.is_err());
}

#[test]
fn owner_pubkey_from_canonical_bytes_accepts_the_modulus_minus_one() {
    // given the canonical encoding of BN254's largest scalar
    let bytes = modulus_minus_one_bytes();
    // when it is decoded as an owner pubkey
    let decoded = OwnerPubkey::from_canonical_bytes(bytes);
    // then it is accepted
    assert!(decoded.is_ok());
}

#[test]
fn owner_pubkey_from_canonical_bytes_rejects_the_modulus() {
    // given the big-endian encoding of the scalar field modulus
    let bytes = modulus_bytes();
    // when it is decoded as an owner pubkey
    let decoded = OwnerPubkey::from_canonical_bytes(bytes);
    // then the reduce-and-compare check rejects it
    assert!(decoded.is_err());
}

#[test]
fn owner_pubkey_from_canonical_bytes_rejects_an_all_ones_string() {
    // given a byte string far above the modulus
    let bytes = [0xffu8; 32];
    // when it is decoded as an owner pubkey
    let decoded = OwnerPubkey::from_canonical_bytes(bytes);
    // then it is rejected rather than silently reduced
    assert!(decoded.is_err());
}

#[test]
fn secret_scalar_from_canonical_bytes_accepts_the_modulus_minus_one() {
    // given the canonical encoding of BN254's largest scalar
    let bytes = modulus_minus_one_bytes();
    // when it is decoded as a secret scalar
    let decoded = SecretScalar::from_canonical_bytes(bytes);
    // then it is accepted
    assert!(decoded.is_ok());
}

#[test]
fn secret_scalar_from_canonical_bytes_rejects_the_modulus() {
    // given the big-endian encoding of the scalar field modulus
    let bytes = modulus_bytes();
    // when it is decoded as a secret scalar
    let decoded = SecretScalar::from_canonical_bytes(bytes);
    // then the reduce-and-compare check rejects it
    assert!(decoded.is_err());
}

#[test]
fn secret_scalar_from_canonical_bytes_rejects_an_all_ones_string() {
    // given a byte string far above the modulus
    let bytes = [0xffu8; 32];
    // when it is decoded as a secret scalar
    let decoded = SecretScalar::from_canonical_bytes(bytes);
    // then it is rejected rather than silently reduced
    assert!(decoded.is_err());
}

#[test]
fn spending_key_random_draws_are_canonical_and_distinct() {
    // given a seeded generator
    let mut rng = ChaCha20Rng::seed_from_u64(SEED);
    // when two spending keys are drawn from it
    let first = SpendingKey::random(&mut rng);
    let second = SpendingKey::random(&mut rng);
    // then both scalars re-encode canonically and the two draws differ
    let first_bytes = *first.scalar().expose_bytes();
    let second_bytes = *second.scalar().expose_bytes();
    assert!(SecretScalar::from_canonical_bytes(first_bytes).is_ok());
    assert!(SecretScalar::from_canonical_bytes(second_bytes).is_ok());
    assert_ne!(first_bytes, second_bytes);
}

#[test]
fn spending_key_debug_redacts_the_scalar() {
    // given a spending key drawn from a seeded generator
    let mut rng = ChaCha20Rng::seed_from_u64(SEED);
    let key = SpendingKey::random(&mut rng);
    let scalar_hex = hex_of(key.scalar().expose_bytes());
    // when it is rendered with Debug
    let rendered = format!("{key:?}");
    // then it shows only the redaction marker and leaks no byte of the scalar
    assert_eq!(rendered, "SpendingKey(REDACTED)");
    assert!(!rendered.contains(&scalar_hex[..8]));
}

#[test]
fn secret_scalar_debug_redacts_the_revealed_bytes() {
    // given the scalar revealed by a spending key drawn from a seeded generator
    let mut rng = ChaCha20Rng::seed_from_u64(SEED);
    let scalar = SpendingKey::random(&mut rng).scalar();
    let scalar_hex = hex_of(scalar.expose_bytes());
    // when it is rendered with Debug
    let rendered = format!("{scalar:?}");
    // then it shows only the redaction marker and leaks no byte of the revealed scalar
    assert_eq!(rendered, "SecretScalar(REDACTED)");
    assert!(!rendered.contains(&scalar_hex[..8]));
}

#[test]
fn owner_pubkey_debug_renders_lowercase_hex_of_its_bytes() {
    // given an owner pubkey built from the field element one
    let pubkey = OwnerPubkey::from_field(Fr::from(1u64));
    // when it is rendered with Debug
    let rendered = format!("{pubkey:?}");
    // then it wraps the 64-character lowercase hex encoding of to_bytes
    assert_eq!(
        rendered,
        format!("OwnerPubkey({})", hex_of(&pubkey.to_bytes()))
    );
}

#[test]
fn secret_scalar_expose_bytes_round_trips_through_from_canonical_bytes() {
    // given the scalar revealed by a freshly drawn spending key
    let mut rng = ChaCha20Rng::seed_from_u64(SEED);
    let scalar = SpendingKey::random(&mut rng).scalar();
    // when its exposed bytes are re-decoded
    let decoded = SecretScalar::from_canonical_bytes(*scalar.expose_bytes())
        .expect("a freshly drawn scalar's own bytes are canonical");
    // then the recovered field element matches the exposed field value
    assert_eq!(decoded.expose_field(), scalar.expose_field());
}

#[test]
fn secret_scalar_expose_field_agrees_with_owner_pubkey_to_field_for_the_same_bytes() {
    // given the canonical encoding of the field element seven
    let bytes = OwnerPubkey::from_field(Fr::from(7u64)).to_bytes();
    // when the same bytes are decoded once as a secret scalar and once as an owner pubkey
    let scalar =
        SecretScalar::from_canonical_bytes(bytes).expect("seven's encoding is canonical");
    let pubkey =
        OwnerPubkey::from_canonical_bytes(bytes).expect("seven's encoding is canonical");
    // then both expose the same field element
    assert_eq!(scalar.expose_field(), pubkey.to_field());
}

#[test]
fn derive_owner_pubkey_is_deterministic_for_one_key() {
    // given a spending key drawn from a seeded generator
    let mut rng = ChaCha20Rng::seed_from_u64(SEED);
    let key = SpendingKey::random(&mut rng);
    // when the owner pubkey is derived twice
    let first = key.derive_owner_pubkey();
    let second = key.derive_owner_pubkey();
    // then both derivations agree
    assert_eq!(first, second);
}

#[test]
fn derive_owner_pubkey_differs_across_distinct_keys() {
    // given two spending keys drawn from one seeded generator
    let mut rng = ChaCha20Rng::seed_from_u64(SEED);
    let first_key = SpendingKey::random(&mut rng);
    let second_key = SpendingKey::random(&mut rng);
    // when their owner pubkeys are derived
    let first_pubkey = first_key.derive_owner_pubkey();
    let second_pubkey = second_key.derive_owner_pubkey();
    // then the two distinct keys produce distinct credentials
    assert_ne!(first_pubkey, second_pubkey);
}

#[test]
fn owner_pubkey_from_field_round_trips_through_to_field() {
    // given the field element three
    let value = Fr::from(3u64);
    // when it is wrapped as an owner pubkey and unwrapped again
    let recovered = OwnerPubkey::from_field(value).to_field();
    // then the field element survives unchanged
    assert_eq!(recovered, value);
}

#[test]
fn owner_pubkey_from_canonical_bytes_of_from_field_closes_the_derivation_seam() {
    // given the owner pubkey built from the field element three
    let pubkey = OwnerPubkey::from_field(Fr::from(3u64));
    // when its bytes are decoded again through from_canonical_bytes
    let decoded = OwnerPubkey::from_canonical_bytes(pubkey.to_bytes());
    // then the external-derivation seam closes on the same pubkey
    assert_eq!(decoded, Ok(pubkey));
}

#[test]
fn owner_pubkey_eq_and_hash_agree_across_construction_routes() {
    // given one field element reached by from_field and by from_canonical_bytes
    let via_field = OwnerPubkey::from_field(Fr::from(9u64));
    let via_bytes = OwnerPubkey::from_canonical_bytes(via_field.to_bytes())
        .expect("from_field always yields a canonical encoding");
    // when both are inserted into a hash set
    let mut set = HashSet::new();
    set.insert(via_field);
    set.insert(via_bytes);
    // then they compare equal and collapse to one entry
    assert_eq!(via_field, via_bytes);
    assert_eq!(set.len(), 1);
}

/// Reads the credential off any spend authority whose field is BN254's `Fr`,
/// proving the forwarding impl on `&A` is usable wherever `A` is.
fn credential_of<A>(authority: A) -> OwnerPubkey
where
    A: SpendAuthority<Field = Fr>,
    A::Error: core::fmt::Debug,
{
    authority
        .owner_pubkey()
        .expect("an in-memory spend authority never fails to derive")
}

#[test]
fn spend_authority_on_spending_key_and_its_reference_agree_with_derive_owner_pubkey() {
    // given a spending key drawn from a seeded generator
    let mut rng = ChaCha20Rng::seed_from_u64(SEED);
    let key = SpendingKey::random(&mut rng);
    let expected = key.derive_owner_pubkey();
    // when the credential is read through SpendAuthority, once by reference and once by value
    let via_reference = credential_of(&key);
    let via_value = credential_of(key);
    // then both agree with the inherent derivation
    assert_eq!(via_reference, expected);
    assert_eq!(via_value, expected);
}

#[test]
fn spend_authority_scalar_on_spending_key_matches_the_inherent_scalar() {
    // given a spending key drawn from a seeded generator
    let mut rng = ChaCha20Rng::seed_from_u64(SEED);
    let key = SpendingKey::random(&mut rng);
    // when the scalar is read through SpendAuthority instead of the inherent method
    let via_trait =
        SpendAuthority::scalar(&key).expect("an in-memory key always reveals its scalar");
    // then it matches the inherent scalar's exposed field element
    assert_eq!(via_trait.expose_field(), key.scalar().expose_field());
}

#[test]
fn secret_types_wipe_themselves_on_drop() {
    // given a bound only a type with a zeroizing Drop can satisfy
    fn wipes_on_drop<T: ZeroizeOnDrop>() {}
    // when it is applied to the two secret-bearing spend types
    wipes_on_drop::<SpendingKey>();
    wipes_on_drop::<SecretScalar>();
    // then both carry the impl, so a dropped key does not leave its bytes behind
}

#[cfg(feature = "test-helpers")]
mod sealed_custody {
    use keystem::{
        NotExportable,
        SpendAuthority,
        curves::bn254::{
            Fr,
            OwnerPubkey,
        },
        test_util::SealedCustody,
    };

    #[test]
    fn sealed_custody_returns_its_enrolled_pubkey_and_refuses_to_export_the_scalar() {
        // given custody enrolled with a known owner pubkey
        let owner_pubkey = OwnerPubkey::from_field(Fr::from(5u64));
        let custody = SealedCustody::enrolled(owner_pubkey);
        // when its credential and its scalar are both requested
        let returned_pubkey = custody.owner_pubkey();
        let returned_scalar = custody.scalar();
        // then the pubkey comes back and the scalar reveal is refused
        assert_eq!(returned_pubkey, Ok(owner_pubkey));
        assert_eq!(returned_scalar.unwrap_err(), NotExportable);
    }
}

#[cfg(feature = "serde")]
mod owner_pubkey_serde {
    use keystem::curves::bn254::{
        Fr,
        OwnerPubkey,
    };

    use super::modulus_bytes;

    #[test]
    fn owner_pubkey_round_trips_through_serde_json() {
        // given an owner pubkey built from the field element two
        let pubkey = OwnerPubkey::from_field(Fr::from(2u64));
        // when it is serialized to JSON and deserialized back
        let json = serde_json::to_string(&pubkey).expect("owner pubkeys serialize");
        let decoded: OwnerPubkey =
            serde_json::from_str(&json).expect("its own JSON deserializes");
        // then the recovered pubkey matches the original
        assert_eq!(decoded, pubkey);
    }

    #[test]
    fn owner_pubkey_deserialize_rejects_a_json_encoding_of_the_modulus() {
        // given a JSON byte array encoding the scalar field modulus
        let json =
            serde_json::to_string(&modulus_bytes()).expect("a byte array serializes");
        // when it is deserialized as an owner pubkey
        let decoded: Result<OwnerPubkey, _> = serde_json::from_str(&json);
        // then the checked decode rejects it as a deserialization error
        assert!(decoded.is_err());
    }
}

#[cfg(feature = "expose-secret-serde")]
mod spending_key_serde {
    use keystem::curves::bn254::SpendingKey;
    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;

    use super::SEED;

    #[test]
    fn spending_key_round_trips_through_serde_json_and_derives_the_same_owner_pubkey() {
        // given a spending key drawn from a seeded generator
        let mut rng = ChaCha20Rng::seed_from_u64(SEED);
        let key = SpendingKey::random(&mut rng);
        let expected = key.derive_owner_pubkey();
        // when it is serialized to JSON and deserialized back
        let json = serde_json::to_string(&key).expect("spending keys serialize");
        let recovered: SpendingKey =
            serde_json::from_str(&json).expect("its own JSON deserializes");
        // then the recovered key derives the same owner pubkey
        assert_eq!(recovered.derive_owner_pubkey(), expected);
    }
}
