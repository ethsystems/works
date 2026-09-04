use ark_ff::PrimeField;

use crate::spend::{
    OwnerPubkey,
    SecretScalar,
};

/// Custody boundary: operations out, key material stays put.
///
/// Sync by design, matching PKCS#11 and card stacks; a networked custodian
/// blocks inside its own adapter. The in-memory [`SpendingKey`] is one
/// implementation, and HSM, smartcard, and enclave-resident keys are the
/// others, so consumer code never names the storage.
///
/// [`SpendingKey`]: crate::SpendingKey
pub trait SpendAuthority {
    /// Primefield instantiation
    type Field: PrimeField;

    /// Matchable failure; [`Infallible`](core::convert::Infallible) for
    /// in-memory keys.
    type Error: core::error::Error;

    /// The public spend credential. An impl may compute it, cache it from
    /// enrollment, or query the device.
    fn owner_pubkey(&self) -> Result<OwnerPubkey<Self::Field>, Self::Error>;

    /// The one fallible scalar egress, for consumers whose circuits take the
    /// spending key as a private witness. Non-exporting custody returns its
    /// [`NotExportable`] error here.
    ///
    /// [`NotExportable`]: crate::NotExportable
    fn scalar(&self) -> Result<SecretScalar<Self::Field>, Self::Error>;
}

impl<A: SpendAuthority + ?Sized> SpendAuthority for &A {
    type Error = A::Error;
    type Field = A::Field;

    fn owner_pubkey(&self) -> Result<OwnerPubkey<Self::Field>, Self::Error> {
        (**self).owner_pubkey()
    }

    fn scalar(&self) -> Result<SecretScalar<Self::Field>, Self::Error> {
        (**self).scalar()
    }
}
