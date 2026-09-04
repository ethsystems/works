//! BN254 instantiation

#[cfg(feature = "poseidon")]
use core::convert::Infallible;
#[cfg(feature = "poseidon")]
use std::cell::RefCell;

pub use ark_bn254::Fr;
#[cfg(feature = "poseidon")]
use light_poseidon::{
    Poseidon,
    PoseidonHasher,
};

#[cfg(feature = "poseidon")]
use crate::authority::SpendAuthority;

/// Master spend secret over BN254's scalar field.
pub type SpendingKey = crate::spend::SpendingKey<Fr>;

/// Public spend credential over BN254's scalar field.
pub type OwnerPubkey = crate::spend::OwnerPubkey<Fr>;

/// One revealed BN254 scalar.
pub type SecretScalar = crate::spend::SecretScalar<Fr>;

#[cfg(feature = "poseidon")]
thread_local! {
    static POSEIDON1: RefCell<Poseidon<Fr>> = RefCell::new(
        Poseidon::<Fr>::new_circom(1)
            .expect("width 2 is inside light-poseidon's circom parameter range"),
    );
}

#[cfg(feature = "poseidon")]
#[cfg_attr(docsrs, doc(cfg(feature = "poseidon")))]
impl SpendingKey {
    pub fn derive_owner_pubkey(&self) -> OwnerPubkey {
        let image = POSEIDON1.with_borrow_mut(|hasher| {
            hasher
                .hash(&[self.scalar().expose_field()])
                .expect("a width-2 hasher takes exactly one input")
        });
        OwnerPubkey::from_field(image)
    }
}

#[cfg(feature = "poseidon")]
#[cfg_attr(docsrs, doc(cfg(feature = "poseidon")))]
impl SpendAuthority for SpendingKey {
    type Error = Infallible;
    type Field = Fr;

    fn owner_pubkey(&self) -> Result<OwnerPubkey, Infallible> {
        Ok(self.derive_owner_pubkey())
    }

    fn scalar(&self) -> Result<SecretScalar, Infallible> {
        Ok(SpendingKey::scalar(self))
    }
}
