//! Draws a spending key, shows two custody shapes for the same credential,
//! builds two viewing channels, seals a note to one of them, and republishes
//! the two credentials a wallet hands out as JSON.
//!
//! `cargo run -p keystem --example wallet_keys --features poseidon,serde,x25519,test-helpers`

use std::convert::Infallible;

use keystem::{
    SpendAuthority,
    ViewingKey,
    ViewingPubkey,
    curves::bn254::{
        Fr,
        OwnerPubkey,
        SpendingKey,
    },
    family::{
        Compliance,
        Incoming,
    },
    test_util::SealedCustody,
};
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use sealring::{
    Domain,
    X25519,
    open,
    seal,
};

/// Fixed seed, so the printed credentials are reproducible. A wallet draws
/// from an OS CSPRNG.
const SEED: u64 = 42;

/// Bound into the envelope and checked on open.
const AAD: &[u8] = b"wallet-keys-example/v1";

struct WalletDomain;

impl Domain for WalletDomain {
    type Error = Infallible;
    type Note = Vec<u8>;

    const DOMAIN_TAG: &'static str = "keystem-example/v1";

    fn encode_note(note: &Self::Note, out: &mut Vec<u8>) -> Result<(), Self::Error> {
        out.extend_from_slice(note);
        Ok(())
    }

    fn decode_note(bytes: &[u8]) -> Result<Self::Note, Self::Error> {
        Ok(bytes.to_vec())
    }
}

/// Prints the credential, then either the scalar or the reason custody
/// withheld it.
fn describe_authority(label: &str, authority: &impl SpendAuthority<Field = Fr>) {
    let owner_pubkey = authority
        .owner_pubkey()
        .expect("both custody shapes here know their credential");
    println!("{label} owner pubkey: {owner_pubkey:?}");
    match authority.scalar() {
        Ok(_) => println!("{label} scalar: exportable"),
        Err(err) => println!("{label} scalar: {err}"),
    }
}

fn main() {
    let mut rng = ChaCha20Rng::seed_from_u64(SEED);

    // rejection-sampled spending key and the Poseidon1 credential it derives.
    let spending_key = SpendingKey::random(&mut rng);
    println!("spending key debug: {spending_key:?}");
    println!("owner pubkey: {:?}", spending_key.derive_owner_pubkey());

    // the in-memory key exports its scalar on demand.
    describe_authority("in-memory", &spending_key);

    // a non-exporting custodian answers the same credential and refuses the
    // scalar, the shape a PKCS#11 token with CKA_EXTRACTABLE = FALSE presents.
    let custody = SealedCustody::enrolled(spending_key.derive_owner_pubkey());
    describe_authority("sealed custody", &custody);

    // Incoming and Compliance are distinct types, so neither stands in for the
    // other at any call site that names one.
    let incoming: ViewingKey<X25519, Incoming> = ViewingKey::random(&mut rng);
    let compliance: ViewingKey<X25519, Compliance> = ViewingKey::random(&mut rng);
    let incoming_pubkey = incoming.derive_pubkey();
    println!("incoming viewing pubkey: {incoming_pubkey:?}");
    println!(
        "compliance viewing pubkey: {:?}",
        compliance.derive_pubkey()
    );

    // seal to the incoming channel's credential, open with its recipient.
    let note = b"pay alice 5 units".to_vec();
    let envelope =
        seal::<X25519, WalletDomain>(incoming_pubkey.public_key(), &note, AAD, &mut rng)
            .expect("sealing a note to a freshly derived credential succeeds");
    let opened = open::<X25519, WalletDomain, _>(incoming.recipient(), &envelope, AAD)
        .expect("the envelope is well formed")
        .expect("the incoming key opens its own envelope");
    assert_eq!(opened, note);
    println!("opened note: {}", String::from_utf8_lossy(&opened));

    // the two credentials a wallet publishes, round-tripped through JSON.
    let owner_pubkey = spending_key.derive_owner_pubkey();
    let owner_json =
        serde_json::to_string(&owner_pubkey).expect("a 32-byte credential serializes");
    let owner_back: OwnerPubkey =
        serde_json::from_str(&owner_json).expect("our own encoding decodes");
    assert_eq!(owner_pubkey, owner_back);
    println!("owner pubkey json: {owner_json}");

    let viewing_json =
        serde_json::to_string(&incoming_pubkey).expect("a curve point serializes");
    let viewing_back: ViewingPubkey<X25519, Incoming> =
        serde_json::from_str(&viewing_json).expect("our own encoding decodes");
    assert_eq!(incoming_pubkey, viewing_back);
    println!("incoming viewing pubkey json: {viewing_json}");
}
