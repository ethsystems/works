#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
use core::fmt;
#[cfg(feature = "std")]
use std::vec::Vec;

use ark_ff::PrimeField;
use sealring::Kem;

use crate::{
    encoding::KEY_LEN,
    error::InvalidAddress,
    spend::OwnerPubkey,
    viewing::ViewingPubkey,
};

/// The two credentials a wallet publishes, as one value.
///
/// Held apart, an owner pubkey and a viewing pubkey are two things a consumer
/// authenticates separately, or forgets to: swapping the viewing half leaves
/// the spend half intact and nothing in the types notices. Held together,
/// substituting either half produces a different `Address`, so there is one
/// value to authenticate instead of two.
///
/// That is the whole property. An address is not self-certifying: checking a
/// viewing pubkey against an owner pubkey needs the spending key, and the owner
/// pubkey is a one-way image of it. Where an address came from is still an
/// out-of-band question.
pub struct Address<F: PrimeField, K: Kem, Fam> {
    owner: OwnerPubkey<F>,
    viewing: ViewingPubkey<K, Fam>,
}

impl<F: PrimeField, K: Kem, Fam> Address<F, K, Fam> {
    /// Pairs the credentials of one wallet.
    pub fn new(owner: OwnerPubkey<F>, viewing: ViewingPubkey<K, Fam>) -> Self {
        Self { owner, viewing }
    }

    /// The public spend credential note commitments carry.
    pub fn owner_pubkey(&self) -> OwnerPubkey<F> {
        self.owner
    }

    /// The read credential for this disclosure channel.
    pub fn viewing_pubkey(&self) -> &ViewingPubkey<K, Fam> {
        &self.viewing
    }

    /// The wire encoding: the owner pubkey, then the viewing pubkey.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(KEY_LEN + K::EPK_LEN);
        bytes.extend_from_slice(&self.owner.to_bytes());
        bytes.extend_from_slice(self.viewing.to_bytes().as_ref());
        bytes
    }

    /// Total decode. Both halves are checked by the type that owns them.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, InvalidAddress> {
        let (owner, viewing) =
            bytes.split_first_chunk::<KEY_LEN>().ok_or(InvalidAddress)?;
        Ok(Self::new(
            OwnerPubkey::from_canonical_bytes(*owner).map_err(|_| InvalidAddress)?,
            ViewingPubkey::from_bytes(viewing).map_err(|_| InvalidAddress)?,
        ))
    }
}

impl<F: PrimeField, K: Kem, Fam> Clone for Address<F, K, Fam>
where
    K::PublicKey: Clone,
{
    fn clone(&self) -> Self {
        Self::new(self.owner, self.viewing.clone())
    }
}

impl<F: PrimeField, K: Kem, Fam> PartialEq for Address<F, K, Fam> {
    fn eq(&self, other: &Self) -> bool {
        self.owner == other.owner && self.viewing == other.viewing
    }
}

impl<F: PrimeField, K: Kem, Fam> Eq for Address<F, K, Fam> {}

impl<F: PrimeField, K: Kem, Fam> fmt::Debug for Address<F, K, Fam> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Address")
            .field("owner", &self.owner)
            .field("viewing", &self.viewing)
            .finish()
    }
}

#[cfg(feature = "serde")]
mod address_serde {
    use serde::{
        Deserialize,
        Deserializer,
        Serialize,
        Serializer,
        de::Error,
    };

    use super::*;

    #[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
    impl<F: PrimeField, K: Kem, Fam> Serialize for Address<F, K, Fam> {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.serialize_bytes(&self.to_bytes())
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
    impl<'de, F: PrimeField, K: Kem, Fam> Deserialize<'de> for Address<F, K, Fam> {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            let bytes = Vec::<u8>::deserialize(deserializer)?;
            Self::from_bytes(&bytes).map_err(D::Error::custom)
        }
    }
}
