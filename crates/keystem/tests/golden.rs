#![cfg(feature = "poseidon")]

use keystem::curves::bn254::SpendingKey;

fn decode_hex(hex: &str) -> Vec<u8> {
    let hex = hex.trim();
    (0..hex.len())
        .step_by(2)
        .map(|i| {
            u8::from_str_radix(&hex[i..i + 2], 16).expect("golden vector is valid hex")
        })
        .collect()
}

fn encode_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Vector is circomlib's `poseidon([1])` over BN254
#[test]
fn derive_owner_pubkey_matches_the_circomlib_poseidon_one_vector() {
    // given a spending key built from the canonical encoding of the field element one
    let mut bytes = [0u8; 32];
    bytes[31] = 0x01;
    let key = SpendingKey::from_canonical_bytes(bytes)
        .expect("one is a canonical field element");
    // when the owner pubkey is derived
    let pubkey = key.derive_owner_pubkey();
    // then its bytes match circomlib's frozen poseidon([1]) vector
    let expected = decode_hex(include_str!("golden/poseidon1.hex"));
    assert_eq!(encode_hex(&pubkey.to_bytes()), encode_hex(&expected));
}
