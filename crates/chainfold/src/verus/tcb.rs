//! Trusted base (plan A6). Every item here is assumed, not proved, and carries its
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
    position::Position,
    verus::model::{
        fview,
        pos_cmp,
    },
};

verus! {

// A6: Clone preserves the fold view (A3 clone fidelity). Verus knows only that a clone of
// a generic `F` satisfies `F::clone`'s unknown ensures; the `Fold` contract adds this.
#[verifier::external_body]
pub proof fn axiom_clone_preserves_fview<F: Clone>(a: F, b: F)
    requires
        cloned(a, b),
    ensures
        fview::<F>(&a) == fview::<F>(&b),
{
}

// A6: the derived `PartialOrd` on `Position` is `lt` (T1 bridge). Verus ignores derives;
// the derive compares fields in declaration order, block then log index, as checked by
// `position_order_is_block_then_log_index`.
impl vstd::std_specs::cmp::PartialOrdSpecImpl for Position {
    open spec fn obeys_partial_cmp_spec() -> bool {
        true
    }

    open spec fn partial_cmp_spec(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(pos_cmp(*self, *other))
    }
}

// A6: the derived `Ord` on `Position` is `lt` (T1 bridge), as for `PartialOrd` above.
impl vstd::std_specs::cmp::OrdSpecImpl for Position {
    open spec fn obeys_cmp_spec() -> bool {
        true
    }

    open spec fn cmp_spec(&self, other: &Self) -> core::cmp::Ordering {
        pos_cmp(*self, *other)
    }
}

// A6: `into_boxed_slice` keeps the elements in order (std docs; vstd has no spec). Used
// by `BlockRing::with_capacity` (P4).
pub assume_specification<T, A: core::alloc::Allocator>[ Vec::<T, A>::into_boxed_slice ](
    v: Vec<T, A>,
) -> (b: Box<[T], A>)
    ensures
        b@ == v@,
;

// A6: `sort_unstable_by_key` permutes the slice (std docs; vstd has no spec). Claims
// nothing about order, because `Batch::validate` checks it. Used by `group_into` (P8).
pub assume_specification<T, K: Ord, F: FnMut(&T) -> K>[ <[T]>::sort_unstable_by_key::<K, F> ](
    v: &mut [T],
    f: F,
)
    ensures
        final(v)@.to_multiset() == old(v)@.to_multiset(),
;

// A6: `split_last_chunk` splits off the last `N` elements (std docs; vstd has no spec).
// Used by `decode_snapshot` (P7).
pub assume_specification<T, const N: usize>[ <[T]>::split_last_chunk::<N> ](s: &[T]) -> (r: Option<
    (&[T], &[T; N]),
>)
    ensures
        s@.len() < N ==> r is None,
        s@.len() >= N ==> (r matches Some((init, last)) && init@ == s@.subrange(
            0,
            s@.len() - N,
        ) && last@ == s@.subrange(s@.len() - N, s@.len() as int)),
;

// A6: empty contract, it asserts nothing. `decode_snapshot` (P7) calls the checksum; its
// safety comes from the checks after it, so the checksum's value is never trusted.
#[cfg(feature = "wincode")]
pub assume_specification[ crate::snapshot::crc32c ](bytes: &[u8]) -> u32;

// A6: an opaque type, it asserts nothing. The codec's error type, named by `deserialize`
// below; decode maps every error to `SnapshotError::Envelope` without reading it.
#[cfg(feature = "wincode")]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExReadError(wincode::ReadError);

// A6: empty contract, it asserts nothing. `decode_snapshot` (P7) checks every field of the
// decoded envelope itself, so no property of the codec is trusted (plan T6c). The entry is on
// the crate's one-line wrapper, so the codec's config types and traits stay out of the proofs.
#[cfg(feature = "wincode")]
pub assume_specification[ crate::snapshot::read_envelope ](payload: &[u8]) -> wincode::ReadResult<
    crate::snapshot::Envelope,
>;

// A6: empty contract, it asserts nothing, and `out` may hold anything afterwards. The encode
// path (`write_envelope`, P7b) calls the codec's serializer through the crate's one-line
// wrapper, as for `read_envelope`. Its only use of the result is a length check it makes
// itself, so no property of the codec is trusted; the bytes are A5.
#[cfg(feature = "wincode")]
pub assume_specification[ crate::snapshot::write_payload ](
    out: &mut Vec<u8>,
    envelope: &crate::snapshot::Envelope,
) -> bool;

// A6: empty contract, it asserts nothing. `write_envelope` (P7b) appends the trailer bytes
// to a buffer whose content no proof reads, so their value is never trusted. The entry is
// on a one-line wrapper because `u32::to_le_bytes`'s array length is a const expression
// that `assume_specification` cannot match.
#[cfg(feature = "wincode")]
pub assume_specification[ crate::snapshot::trailer_bytes ](crc: u32) -> [u8; 4];

// A6: asserts nothing. `Spans` opts out of vstd's iterator laws, so verified callers
// learn nothing from `Spans::next`; this lets `next` and `size_hint` verify panic-free.
// A lawful spec would need `remaining()` as a sequence of slice references, which spec
// code cannot build. No verified code iterates `Spans`; the engine uses `Batch::span`.
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

// A6: asserts nothing, as for `Spans`. `Observed` opts out of vstd's iterator laws; the
// sequence it yields is `Observed@`, which `BlockRing::iter` fixes.
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
