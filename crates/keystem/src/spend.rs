use core::{
    fmt,
    marker::PhantomData,
};

use ark_ff::PrimeField;
use rand_core::CryptoRng;
use zeroize::{
    Zeroize,
    ZeroizeOnDrop,
};

use crate::{
    encoding::{
        self,
        KEY_LEN,
    },
    error::NonCanonical,
    hex::write_hex,
};

/// Master spend secret over any prime field within the 256-bit width bound.
///
/// Holds the field's canonical big-endian encoding and is canonical by
/// construction: rejection sampling or checked decode are the only ways in.
/// Zeroized on drop, `Debug` prints `REDACTED`.
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct SpendingKey<F: PrimeField> {
    bytes: [u8; KEY_LEN],
    #[zeroize(skip)]
    field: PhantomData<fn() -> F>,
}

impl<F: PrimeField> SpendingKey<F> {
    /// Uniform over `F` by rejection sampling.
    pub fn random(rng: &mut impl CryptoRng) -> Self {
        Self::from_canonical(encoding::sample_canonical::<F>(rng))
    }

    /// Total decode
    pub fn from_canonical_bytes(bytes: [u8; KEY_LEN]) -> Result<Self, NonCanonical> {
        encoding::check_canonical::<F>(&bytes)?;
        Ok(Self::from_canonical(bytes))
    }

    /// Infallible reveal.
    pub fn scalar(&self) -> SecretScalar<F> {
        SecretScalar {
            bytes: self.bytes,
            field: PhantomData,
        }
    }

    /// Wraps bytes a caller has already proven canonical.
    fn from_canonical(bytes: [u8; KEY_LEN]) -> Self {
        Self {
            bytes,
            field: PhantomData,
        }
    }
}

impl<F: PrimeField> fmt::Debug for SpendingKey<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SpendingKey(REDACTED)")
    }
}

/// Public spend credential, the value note commitments carry.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct OwnerPubkey<F: PrimeField> {
    bytes: [u8; KEY_LEN],
    field: PhantomData<fn() -> F>,
}

impl<F: PrimeField> OwnerPubkey<F> {
    /// Total decode, the counterparty-import path. Rejects bytes at or above
    /// the modulus.
    pub fn from_canonical_bytes(bytes: [u8; KEY_LEN]) -> Result<Self, NonCanonical> {
        encoding::check_canonical::<F>(&bytes)?;
        Ok(Self {
            bytes,
            field: PhantomData,
        })
    }

    /// The seam for consumers whose derivation lives outside this crate:
    /// `scalar` to `expose_field` to their hash to `from_field`.
    pub fn from_field(value: F) -> Self {
        Self {
            bytes: encoding::to_canonical_bytes(value),
            field: PhantomData,
        }
    }

    /// The canonical big-endian encoding.
    pub fn to_bytes(&self) -> [u8; KEY_LEN] {
        self.bytes
    }

    /// Infallible: the canonical invariant holds by construction.
    pub fn to_field(&self) -> F {
        encoding::to_field(&self.bytes)
    }
}

impl<F: PrimeField> fmt::Debug for OwnerPubkey<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("OwnerPubkey(")?;
        write_hex(f, &self.bytes)?;
        f.write_str(")")
    }
}

/// One revealed scalar with one owner: zeroizing, canonical.
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct SecretScalar<F: PrimeField> {
    bytes: [u8; KEY_LEN],
    #[zeroize(skip)]
    field: PhantomData<fn() -> F>,
}

impl<F: PrimeField> SecretScalar<F> {
    /// Total decode
    pub fn from_canonical_bytes(bytes: [u8; KEY_LEN]) -> Result<Self, NonCanonical> {
        encoding::check_canonical::<F>(&bytes)?;
        Ok(Self {
            bytes,
            field: PhantomData,
        })
    }

    /// The canonical big-endian encoding of the revealed scalar.
    pub fn expose_bytes(&self) -> &[u8; KEY_LEN] {
        &self.bytes
    }

    /// The revealed scalar as a field element.
    pub fn expose_field(&self) -> F {
        encoding::to_field(&self.bytes)
    }
}

impl<F: PrimeField> fmt::Debug for SecretScalar<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SecretScalar(REDACTED)")
    }
}

#[cfg(feature = "serde")]
mod owner_pubkey_serde {
    use serde::{
        Deserialize,
        Deserializer,
        Serialize,
        Serializer,
        de::Error,
    };

    use super::*;

    #[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
    impl<F: PrimeField> Serialize for OwnerPubkey<F> {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            self.bytes.serialize(serializer)
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
    impl<'de, F: PrimeField> Deserialize<'de> for OwnerPubkey<F> {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            let bytes = <[u8; KEY_LEN]>::deserialize(deserializer)?;
            Self::from_canonical_bytes(bytes).map_err(D::Error::custom)
        }
    }
}

#[cfg(feature = "expose-secret-serde")]
mod spending_key_serde {
    use serde::{
        Deserialize,
        Deserializer,
        Serialize,
        Serializer,
        de::Error,
    };

    use super::*;

    #[cfg_attr(docsrs, doc(cfg(feature = "expose-secret-serde")))]
    impl<F: PrimeField> Serialize for SpendingKey<F> {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            self.bytes.serialize(serializer)
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "expose-secret-serde")))]
    impl<'de, F: PrimeField> Deserialize<'de> for SpendingKey<F> {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            let bytes = <[u8; KEY_LEN]>::deserialize(deserializer)?;
            Self::from_canonical_bytes(bytes).map_err(D::Error::custom)
        }
    }
}
