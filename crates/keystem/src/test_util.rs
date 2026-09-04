//! Test helpers: custody that refuses export, and a conformance suite third
//! party [`KemKeyOps`] adapters should run against their own keys.

#[cfg(feature = "spend")]
use ark_ff::PrimeField;
#[cfg(feature = "viewing")]
use rand_core::CryptoRng;

#[cfg(feature = "viewing")]
use crate::kem_ops::KemKeyOps;
#[cfg(feature = "spend")]
use crate::{
    authority::SpendAuthority,
    error::NotExportable,
    spend::{
        OwnerPubkey,
        SecretScalar,
    },
};

/// Longest secret-key encoding the conformance probes cover.
#[cfg(feature = "viewing")]
const MAX_PROBE_LEN: usize = 256;

/// Custody that enrolls a credential and refuses every reveal, the shape an
/// HSM presents to a circuit that wants the spending key as a witness.
#[cfg(feature = "spend")]
#[cfg_attr(docsrs, doc(cfg(feature = "spend")))]
pub struct SealedCustody<F: PrimeField> {
    owner_pubkey: OwnerPubkey<F>,
}

#[cfg(feature = "spend")]
#[cfg_attr(docsrs, doc(cfg(feature = "spend")))]
impl<F: PrimeField> SealedCustody<F> {
    /// Enrolls a credential whose scalar the device will never release.
    pub fn enrolled(owner_pubkey: OwnerPubkey<F>) -> Self {
        Self { owner_pubkey }
    }
}

#[cfg(feature = "spend")]
#[cfg_attr(docsrs, doc(cfg(feature = "spend")))]
impl<F: PrimeField> SpendAuthority for SealedCustody<F> {
    type Error = NotExportable;
    type Field = F;

    fn owner_pubkey(&self) -> Result<OwnerPubkey<F>, NotExportable> {
        Ok(self.owner_pubkey)
    }

    fn scalar(&self) -> Result<SecretScalar<F>, NotExportable> {
        Err(NotExportable)
    }
}

/// Asserts `decode_sk` inverts `encode_sk` for `sk`, and that the recovered
/// key derives the same public key.
#[cfg(feature = "viewing")]
#[cfg_attr(docsrs, doc(cfg(feature = "viewing")))]
pub fn conformance_sk_codec_roundtrips<K: KemKeyOps>(sk: &K::SecretKey) {
    let encoded = K::encode_sk(sk);
    let decoded = K::decode_sk(encoded.as_ref()).expect("own sk encoding must decode");
    assert_eq!(
        K::encode_sk(&decoded).as_ref(),
        encoded.as_ref(),
        "decode_sk must invert encode_sk"
    );
    assert_eq!(
        K::encode_pk(&K::derive_pk(&decoded)).as_ref(),
        K::encode_pk(&K::derive_pk(sk)).as_ref(),
        "a decoded sk must derive the public key its encoding came from"
    );
}

/// Asserts a generated key survives both codecs and that two draws from one
/// generator differ.
#[cfg(feature = "viewing")]
#[cfg_attr(docsrs, doc(cfg(feature = "viewing")))]
pub fn conformance_generate_sk_draws<K: KemKeyOps>(rng: &mut impl CryptoRng) {
    let first = K::generate_sk(rng);
    let second = K::generate_sk(rng);
    conformance_sk_codec_roundtrips::<K>(&first);
    assert_ne!(
        K::encode_sk(&first).as_ref(),
        K::encode_sk(&second).as_ref(),
        "two draws from one generator must differ"
    );
}

/// Asserts byte strings of the wrong length decode to no secret key: the
/// empty string, and lengths shorter and longer than the encoding.
#[cfg(feature = "viewing")]
#[cfg_attr(docsrs, doc(cfg(feature = "viewing")))]
pub fn conformance_wrong_length_fails<K: KemKeyOps>(sk: &K::SecretKey) {
    let len = K::encode_sk(sk).as_ref().len();
    assert!(
        (1..MAX_PROBE_LEN).contains(&len),
        "conformance probes cover secret-key encodings up to {MAX_PROBE_LEN} bytes"
    );

    let probe = [0xAAu8; MAX_PROBE_LEN];
    for case in [&probe[..0], &probe[..len - 1], &probe[..len + 1]] {
        assert!(
            K::decode_sk(case).is_none(),
            "an sk encoding of {} bytes must not decode",
            case.len()
        );
    }
}
