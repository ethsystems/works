//! Trusted base. Every item here is assumed, not proved, and carries its
//! justification. `verus-gates.py` rejects trusted constructs anywhere else.

#[cfg(not(feature = "std"))]
use alloc::{
    boxed::Box,
    vec::Vec,
};
#[cfg(feature = "std")]
use std::{
    boxed::Box,
    vec::Vec,
};

use vstd::prelude::*;

use crate::{
    fold::Fold,
    position::Position,
    sink::NoSink,
    verus::model::{
        fview,
        sink_offered,
    },
};

verus! {

// Trusted: Clone preserves the fold view (clone fidelity, stated on `Fold`). Verus knows
// only that a clone of a generic `F` satisfies `F::clone`'s unknown ensures; the `Fold`
// contract adds this, so the bound is `Fold`, not every `Clone` type.
#[verifier::external_body]
pub proof fn axiom_clone_preserves_fview<F: Fold + Clone>(a: F, b: F)
    requires
        cloned(a, b),
    ensures
        fview::<F>(&a) == fview::<F>(&b),
{
}

// Trusted: sink honesty for `NoSink`, which stores nothing, so no offer is ever held.
// `sink_offered` is uninterpreted, so the unit sink's empty set is stated here.
#[verifier::external_body]
pub proof fn axiom_no_sink_offers_nothing(s: NoSink)
    ensures
        sink_offered::<NoSink>(&s) == Set::<Position>::empty(),
{
}

// Trusted: `into_boxed_slice` keeps the elements in order (std docs; vstd has no spec).
// Used by `BlockRing::with_capacity`.
pub assume_specification<T, A: core::alloc::Allocator>[ Vec::<T, A>::into_boxed_slice ](
    v: Vec<T, A>,
) -> (b: Box<[T], A>)
    ensures
        b@ == v@,
;

// Trusted: `sort_unstable_by_key` permutes the slice (std docs; vstd has no spec). Claims
// nothing about order, because `Batch::validate` checks it. Used by `group_into`.
pub assume_specification<T, K: Ord, F: FnMut(&T) -> K>[ <[T]>::sort_unstable_by_key::<K, F> ](
    v: &mut [T],
    f: F,
)
    ensures
        final(v)@.to_multiset() == old(v)@.to_multiset(),
;

// Trusted: the checksum is a function of the bytes (`crc32c_spec` is uninterpreted, so
// nothing about its value is assumed). Encode writes it and decode compares against it.
#[cfg(feature = "wincode")]
pub assume_specification[ crate::snapshot::crc32c ](bytes: &[u8]) -> (r: u32)
    ensures
        r == crate::snapshot::crc32c_spec(bytes@),
;

// Trusted: an opaque type, it asserts nothing. The codec's error type, named by
// `deserialize` below; decode maps every error to `SnapshotError::Envelope` without
// reading it.
#[cfg(feature = "wincode")]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExReadError(wincode::ReadError);

// Trusted: the codec round trip. Bytes the serializer produces for an envelope decode
// back to that envelope (wincode's derived `SchemaWrite`/`SchemaRead` pair under one
// config; the borrowed and owned tags serialize alike, checked by a test). Only the
// durable round trip reads this: `decode_snapshot` checks every decoded field itself, so
// its safety trusts nothing of the codec. The entry is on the crate's one-line wrapper,
// so the codec's config types and traits stay out of the proofs.
#[cfg(feature = "wincode")]
pub assume_specification[ crate::snapshot::read_envelope ](payload: &[u8]) -> (r: wincode::ReadResult<
    crate::snapshot::Envelope<Vec<u8>>,
>)
    ensures
        forall|e: crate::snapshot::EnvelopeView|
            #[trigger] crate::snapshot::encodable(e) && crate::snapshot::wire(e) == payload@ ==> (r matches Ok(d) && d@ == e),
;

// Trusted: on success the serializer appends exactly its bytes for the envelope, which
// open with the magic and the little-endian version (fixint layout, pinned by a test).
// On failure `out` may hold anything past its old length; `write_envelope` truncates it.
// The state bytes rest on the fold's `Persist` codec.
#[cfg(feature = "wincode")]
pub assume_specification[ crate::snapshot::write_payload ](
    out: &mut Vec<u8>,
    envelope: &crate::snapshot::Envelope<&'static [u8]>,
) -> (r: bool)
    ensures
        r ==> final(out)@ == old(out)@ + crate::snapshot::wire(envelope@)
            && crate::snapshot::encodable(envelope@) && crate::snapshot::wire_layout(envelope@),
;

// Trusted: asserts nothing. `Spans` opts out of vstd's iterator laws, so verified callers
// learn nothing from `Spans::next`; this lets `next` and `size_hint` verify panic-free. A
// lawful spec would need `remaining()` as a sequence of slice references, which spec code
// cannot build. No verified code iterates `Spans`; the engine uses `Batch::span`.
impl<'a, E> vstd::std_specs::iter::IteratorSpecImpl for crate::batch::Spans<'a, E> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        false
    }

    #[verifier::prophetic]
    open spec fn remaining(&self) -> Seq<Self::Item> {
        Seq::empty()
    }

    #[verifier::prophetic]
    open spec fn will_return_none(&self) -> bool {
        false
    }

    open spec fn decrease(&self) -> Option<nat> {
        None
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        None
    }
}

// Trusted: asserts nothing, as for `Spans`. `Observed` opts out of vstd's iterator laws;
// the sequence it yields is `Observed@`, which `BlockRing::iter` fixes.
impl<'a> vstd::std_specs::iter::IteratorSpecImpl for crate::ring::Observed<'a> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        false
    }

    #[verifier::prophetic]
    open spec fn remaining(&self) -> Seq<Self::Item> {
        Seq::empty()
    }

    #[verifier::prophetic]
    open spec fn will_return_none(&self) -> bool {
        false
    }

    open spec fn decrease(&self) -> Option<nat> {
        None
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        None
    }
}

} // verus!
