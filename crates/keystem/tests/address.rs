#![cfg(all(feature = "poseidon", feature = "x25519"))]

use ark_bn254::Fr;
use keystem::{
    Address,
    ViewingKey,
    curves::bn254::SpendingKey,
    family::Incoming,
};
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use sealring::X25519;

type Addr = Address<Fr, X25519, Incoming>;

fn address(seed: u64) -> Addr {
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    Address::new(
        SpendingKey::random(&mut rng).derive_owner_pubkey(),
        ViewingKey::<X25519, Incoming>::random(&mut rng).derive_pubkey(),
    )
}

#[test]
fn round_trips_through_bytes() {
    let alice = address(1);

    assert_eq!(Addr::from_bytes(&alice.to_bytes()).unwrap(), alice);
}

#[test]
fn substituting_the_viewing_half_changes_the_address() {
    let alice = address(1);
    let mallory = address(2);
    let swapped = Address::new(alice.owner_pubkey(), mallory.viewing_pubkey().clone());

    assert_eq!(swapped.owner_pubkey(), alice.owner_pubkey());
    assert_ne!(swapped, alice);
    assert_ne!(swapped.to_bytes(), alice.to_bytes());
}

#[test]
fn a_truncated_or_non_canonical_encoding_is_rejected() {
    let mut bytes = address(1).to_bytes();

    assert!(Addr::from_bytes(&bytes[..bytes.len() - 1]).is_err());
    assert!(Addr::from_bytes(&bytes[..16]).is_err());

    // bit 255 of the viewing half: a second encoding of the same point.
    let last = bytes.len() - 1;
    bytes[last] |= 0x80;
    assert!(Addr::from_bytes(&bytes).is_err());
}

#[cfg(feature = "serde")]
mod address_serde {
    use super::*;

    #[test]
    fn round_trips_through_serde_json() {
        let alice = address(1);
        let json = serde_json::to_vec(&alice).unwrap();

        assert_eq!(serde_json::from_slice::<Addr>(&json).unwrap(), alice);
    }
}
