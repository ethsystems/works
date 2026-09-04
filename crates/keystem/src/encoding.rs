use ark_ff::{
    BigInteger,
    PrimeField,
};
use rand_core::CryptoRng;

use crate::error::NonCanonical;

/// Byte width of every key encoding in this crate.
pub(crate) const KEY_LEN: usize = 32;

/// Limbs an encoding holds, one per 64-bit word.
const KEY_LIMBS: usize = KEY_LEN / 8;

/// Widest modulus the encoding holds. Must stay `KEY_LEN` bytes of bits, or
/// the two width asserts below stop agreeing with each other.
const MAX_MODULUS_BITS: u32 = 256;

/// Width bound, checked at the instantiation that asks for it: a field whose
/// modulus or limb count outgrows the encoding fails to compile, so the limb
/// walks below never truncate.
fn assert_within_width<F: PrimeField>() {
    const {
        assert!(
            F::MODULUS_BIT_SIZE <= MAX_MODULUS_BITS,
            "field modulus is wider than the 256-bit key encoding"
        );
        assert!(
            <F::BigInt as BigInteger>::NUM_LIMBS <= KEY_LIMBS,
            "field limb count is wider than the 256-bit key encoding"
        );
    }
}

/// Canonical big-endian encoding of `value`, zero-padded to [`KEY_LEN`].
pub(crate) fn to_canonical_bytes<F: PrimeField>(value: F) -> [u8; KEY_LEN] {
    assert_within_width::<F>();
    let mut bytes = [0u8; KEY_LEN];
    // limbs run least significant first, so the encoding fills from the back.
    for (chunk, limb) in bytes.rchunks_exact_mut(8).zip(value.into_bigint().as_ref()) {
        chunk.copy_from_slice(&limb.to_be_bytes())
    }
    bytes
}

/// Bytes the encoding pads with above the field's integer form. The width
/// bound keeps this non-negative.
const fn pad_len<F: PrimeField>() -> usize {
    KEY_LEN - <F::BigInt as BigInteger>::NUM_LIMBS * 8
}

/// The big-endian encoding read into the field's integer representation.
///
/// Limbs run least significant first, so the read walks the encoding from the
/// back and never reaches the pad.
fn to_bigint<F: PrimeField>(bytes: &[u8; KEY_LEN]) -> F::BigInt {
    let mut integer = F::BigInt::default();
    for (chunk, limb) in bytes.rchunks_exact(8).zip(integer.as_mut()) {
        *limb =
            u64::from_be_bytes(chunk.try_into().expect("rchunks_exact(8) yields 8 bytes"))
    }
    integer
}

/// The field element for the canonical encoding
pub(crate) fn to_field<F: PrimeField>(bytes: &[u8; KEY_LEN]) -> F {
    assert_within_width::<F>();
    F::from_bigint(to_bigint::<F>(bytes))
        .expect("a canonical encoding sits below the modulus")
}

/// Rejects an encoding that is not a part of the field.
pub(crate) fn check_canonical<F: PrimeField>(
    bytes: &[u8; KEY_LEN],
) -> Result<(), NonCanonical> {
    assert_within_width::<F>();
    let canonical = bytes[..pad_len::<F>()].iter().all(|byte| *byte == 0)
        && to_bigint::<F>(bytes) < F::MODULUS;
    canonical.then_some(()).ok_or(NonCanonical)
}

/// Uniform canonical encoding of a field element drawn by rejection sampling
pub(crate) fn sample_canonical<F: PrimeField>(rng: &mut impl CryptoRng) -> [u8; KEY_LEN] {
    let bits = F::MODULUS_BIT_SIZE as usize;
    let mut bytes = [0u8; KEY_LEN];
    loop {
        let body = &mut bytes[KEY_LEN - bits.div_ceil(8)..];
        rng.fill_bytes(body);
        body[0] &= high_byte_mask(bits);
        if check_canonical::<F>(&bytes).is_ok() {
            return bytes;
        }
    }
}

fn high_byte_mask(bits: usize) -> u8 {
    match bits % 8 {
        0 => u8::MAX,
        used => (1u8 << used) - 1,
    }
}

#[cfg(all(test, feature = "bn254"))]
mod tests {
    use ark_bn254::Fr;
    use ark_ff::{
        One,
        Zero,
    };
    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;

    use super::*;

    #[test]
    fn canonical_bytes_round_trip_through_the_field() {
        // given the multiplicative identity of BN254's scalar field
        let value = Fr::one();
        // when its encoding is checked and read back
        let bytes = to_canonical_bytes(value);
        // then the check accepts and the field element survives unchanged
        assert_eq!(check_canonical::<Fr>(&bytes), Ok(()));
        assert_eq!(to_field::<Fr>(&bytes), value);
    }

    #[test]
    fn to_field_inverts_the_canonical_encoding() {
        // given the two boundary elements and one interior one
        let values = [Fr::zero(), Fr::one(), -Fr::one(), Fr::from(123_456_789u64)];
        // when each is encoded and read back through the unchecked decode
        let recovered = values.map(|value| to_field::<Fr>(&to_canonical_bytes(value)));
        // then every element survives the round trip
        assert_eq!(recovered, values);
    }

    #[test]
    fn to_field_agrees_with_the_reducing_decode() {
        // given canonical encodings drawn from a seeded generator
        let mut rng = ChaCha20Rng::seed_from_u64(0xBEEF);
        let samples: [[u8; KEY_LEN]; 100] =
            core::array::from_fn(|_| sample_canonical::<Fr>(&mut rng));
        // when each is read both by the limb walk and by a full reduction
        let agree = samples
            .iter()
            .all(|s| to_field::<Fr>(s) == Fr::from_be_bytes_mod_order(s));
        // then skipping the reduction names the same field element
        assert!(agree);
    }

    #[test]
    fn zero_encodes_to_an_all_zero_string() {
        // given the additive identity
        let value = Fr::zero();
        // when it is encoded
        let bytes = to_canonical_bytes(value);
        // then every byte of the fixed-width encoding is zero
        assert_eq!(bytes, [0u8; KEY_LEN]);
    }

    #[test]
    fn the_modulus_itself_is_rejected() {
        // given the modulus, the smallest non-canonical encoding
        let mut bytes = [0u8; KEY_LEN];
        bytes.copy_from_slice(&Fr::MODULUS.to_bytes_be());
        // when it is checked
        let checked = check_canonical::<Fr>(&bytes);
        // then the modulus comparison rejects it
        assert_eq!(checked, Err(NonCanonical));
    }

    #[test]
    fn one_below_the_modulus_is_accepted() {
        // given the largest canonical field element
        let bytes = to_canonical_bytes(-Fr::one());
        // when it is checked and read back
        let checked = check_canonical::<Fr>(&bytes);
        // then it is accepted and names the field element it encodes
        assert_eq!(checked, Ok(()));
        assert_eq!(to_field::<Fr>(&bytes), -Fr::one());
    }

    #[test]
    fn an_all_ones_string_is_rejected() {
        // given a byte string far above the modulus
        let bytes = [0xffu8; KEY_LEN];
        // when it is checked
        let checked = check_canonical::<Fr>(&bytes);
        // then it is rejected rather than silently reduced
        assert_eq!(checked, Err(NonCanonical));
    }

    #[test]
    fn sampling_yields_canonical_encodings() {
        // given a seeded generator
        let mut rng = ChaCha20Rng::seed_from_u64(0xC0FFEE);
        // when a hundred candidates are drawn
        let samples: [[u8; KEY_LEN]; 100] =
            core::array::from_fn(|_| sample_canonical::<Fr>(&mut rng));
        // then every one decodes, and the draw is not a constant
        assert!(samples.iter().all(|s| check_canonical::<Fr>(s).is_ok()));
        assert!(samples.windows(2).any(|pair| pair[0] != pair[1]));
    }

    #[test]
    fn the_high_byte_mask_covers_every_modulus_width() {
        // given the bit widths a 32-byte encoding can hold
        let widths = [1usize, 7, 8, 9, 254, 255, 256];
        // when each is masked
        let masks = widths.map(high_byte_mask);
        // then a whole-byte width keeps all eight bits and the rest truncate
        assert_eq!(masks, [0x01, 0x7f, 0xff, 0x01, 0x3f, 0x7f, 0xff]);
    }
}
