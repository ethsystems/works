#![cfg(feature = "bn254")]

use ark_serialize::CanonicalDeserialize;
use keystem::curves::bn254::{
    Fr,
    OwnerPubkey,
};
use proptest::prelude::*;

proptest! {
    /// keystem decodes big-endian; arkworks' canonical serialization is little-endian.
    /// Reversing the byte string aligns the two codecs on the same bit pattern, and
    /// they must accept or reject it together, agreeing on the field element when both do.
    #[test]
    fn owner_pubkey_canonicity_matches_arkworks_little_endian_deserialization(bytes in any::<[u8; 32]>()) {
        // given 32 arbitrary bytes and their byte-reversed form
        let mut reversed = bytes;
        reversed.reverse();
        // when both codecs attempt to decode the same bit pattern
        let via_keystem = OwnerPubkey::from_canonical_bytes(bytes);
        let via_arkworks = Fr::deserialize_compressed(&reversed[..]);
        // then the two codecs agree on acceptance, and on the value when both accept
        prop_assert_eq!(via_keystem.is_ok(), via_arkworks.is_ok());
        if let (Ok(from_keystem), Ok(from_arkworks)) = (via_keystem, via_arkworks) {
            prop_assert_eq!(from_keystem.to_field(), from_arkworks);
        }
    }
}
