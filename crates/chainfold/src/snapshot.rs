//! Engine-owned snapshot envelope: canonical bytes framed with a CRC32C trailer.

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use core::fmt;

use crate::{
    batch::first_descent,
    engine::{
        Engine,
        EngineConfig,
    },
    error::ConfigError,
    fold::Fold,
    position::{
        BlockRef,
        Position,
    },
    ring::BlockRing,
};
#[cfg(verus_keep_ghost)]
use {
    crate::{
        batch::lemma_ascending_pairwise,
        error::EngineStatus,
        verus::model::{
            EngineView,
            SlotView,
            lemma_durable_snapshot,
            prefix_at_or_below,
            ring_ascending,
        },
    },
    vstd::{
        prelude::*,
        string::StringSliceAdditionalSpecFns,
    },
};

/// CRC32C over a slice-by-16 table; the envelope trailer and manifest slots share it.
#[cfg(not(feature = "std"))]
const CRC32C: crc::Crc<u32, crc::Table<16>> =
    crc::Crc::<u32, crc::Table<16>>::new(&crc::CRC_32_ISCSI);

/// Computes the CRC32C of a byte slice from the table.
#[cfg(not(feature = "std"))]
#[inline]
pub(crate) fn crc32c(bytes: &[u8]) -> u32 {
    CRC32C.checksum(bytes)
}

/// Computes the CRC32C of a byte slice on the runtime-detected SIMD path.
#[cfg(feature = "std")]
#[inline]
pub(crate) fn crc32c(bytes: &[u8]) -> u32 {
    crc_fast::crc32_iscsi(bytes)
}

/// Largest length-bearing envelope field the codec accepts, in bytes.
///
/// Engine-owned ceiling replacing the codec's own default: it admits the widest ring
/// the engine configuration allows plus consumer state well past it, and it caps the
/// allocation a length prefix can drive on the decode path.
#[cfg_attr(verus_keep_ghost, verus_verify)]
const MAX_ENVELOPE_FIELD_LEN: usize = 1 << 30;

/// Codec settings of record: fixint little-endian with the engine-owned length ceiling.
type EnvelopeConfig = wincode::config::Configuration<true, MAX_ENVELOPE_FIELD_LEN>;

/// Codec instance the encode and decode paths share.
const ENVELOPE_CONFIG: EnvelopeConfig = EnvelopeConfig::new();

/// Byte length of a `BlockRef` hash.
#[cfg_attr(verus_keep_ghost, verus_verify)]
const HASH_LEN: usize = 32;
/// Byte length of the magic prefix.
#[cfg_attr(verus_keep_ghost, verus_verify)]
const MAGIC_LEN: usize = 8;
/// Byte length of the version field.
#[cfg_attr(verus_keep_ghost, verus_verify)]
const VERSION_LEN: usize = 2;
/// Byte length of the CRC32C trailer.
#[cfg_attr(verus_keep_ghost, verus_verify)]
const CRC_LEN: usize = 4;
/// Smallest possible encoded snapshot: magic, version, and trailer with an empty payload.
#[cfg_attr(verus_keep_ghost, verus_verify)]
const MIN_ENVELOPE_LEN: usize = MAGIC_LEN + VERSION_LEN + CRC_LEN;

/// Fixed 8-byte prefix identifying a chainfold snapshot.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const SNAPSHOT_MAGIC: [u8; 8] = *b"CHNFOLD1";
/// Snapshot envelope wire format version.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const SNAPSHOT_VERSION: u16 = 1;

/// Fold state with a canonical byte encoding and an identity tag.
// No spec: decode checks the bytes it gets from `decode_state`'s caller, and treats the
// decoded fold as opaque (its view is whatever `decode_state` returns).
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait Persist: Fold + Sized {
    /// Identifies the fold type and its state format; mismatch refuses to load.
    const STATE_TAG: &'static str;
    /// Failure decoding state bytes back into the fold.
    type PersistError;

    /// Appends canonical state bytes; identical state must yield identical bytes.
    fn encode_state(&self, out: &mut Vec<u8>);
    /// Decodes state bytes produced by `encode_state`.
    fn decode_state(bytes: &[u8]) -> Result<Self, Self::PersistError>;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, wincode::SchemaWrite, wincode::SchemaRead)]
// `T` holds the tag: the fold's static bytes on encode (no allocation), owned on decode.
// Both serialize as the same length-prefixed bytes.
pub(crate) struct Envelope<T> {
    magic: [u8; 8],
    version: u16,
    tag: T,
    cursor_set: u8,
    cursor_block: u64,
    cursor_log_index: u64,
    ring_numbers: Vec<u64>,
    ring_hashes: Vec<u8>,
    state: Vec<u8>,
}

/// Decodes an envelope payload (the bytes before the trailer).
#[inline]
pub(crate) fn read_envelope(payload: &[u8]) -> wincode::ReadResult<Envelope<Vec<u8>>> {
    wincode::config::deserialize(payload, ENVELOPE_CONFIG)
}

/// Serializes an envelope payload onto `out`; false when a field exceeds the limit.
#[inline]
pub(crate) fn write_payload(
    out: &mut Vec<u8>,
    envelope: &Envelope<&'static [u8]>,
) -> bool {
    wincode::config::serialize_into(&mut *out, envelope, ENVELOPE_CONFIG).is_ok()
}

/// Little-endian bytes of a CRC32C trailer.
#[inline]
pub(crate) fn trailer_bytes(crc: u32) -> [u8; 4] {
    crc.to_le_bytes()
}

/// Serializes an envelope and appends its CRC32C trailer.
///
/// The codec refuses a field longer than `MAX_ENVELOPE_FIELD_LEN`, which is the only
/// way a fixed-shape envelope fails to serialize into a growable buffer.
// The codec only appends; the length check makes that a checked fact, not a trusted one.
#[cfg_attr(verus_keep_ghost, verus_verify)]
fn write_envelope<E>(
    envelope: &Envelope<&'static [u8]>,
    out: &mut Vec<u8>,
) -> Result<(), SnapshotError<E>> {
    let start = out.len();
    if !write_payload(out, envelope) || out.len() < start {
        out.truncate(start);
        return Err(SnapshotError::TooLarge {
            limit: MAX_ENVELOPE_FIELD_LEN,
        });
    }
    let crc = crc32c(&out[start..]);
    out.extend_from_slice(&trailer_bytes(crc));
    Ok(())
}

/// Builds the ring lanes of an envelope from the ring's oldest `len` entries.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        ring.wf(),
        len <= ring@.len(),
    ensures
        lanes(ring@.subrange(0, len as int), r.0@, r.1@),
))]
fn ring_lanes(ring: &BlockRing, len: usize) -> (Vec<u64>, Vec<u8>) {
    let mut numbers = Vec::new();
    let mut hashes = Vec::new();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            ring.wf(),
            len <= ring@.len(),
            lanes(ring@.subrange(0, i as int), numbers@, hashes@),
    ))]
    for i in 0..len {
        let block = ring.get(i);
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost old_hashes = hashes@;
        }
        numbers.push(block.number);
        hashes.extend_from_slice(&block.hash);
        #[cfg(verus_keep_ghost)]
        proof! {
            let r = ring@.subrange(0, i + 1);
            let prev = ring@.subrange(0, i as int);
            assert(r[i as int] == block);
            assert forall|k: int| 0 <= k < i + 1 implies #[trigger] r[k].number == numbers@[k]
                && r[k].hash@ == hashes@.subrange(32 * k, 32 * k + 32) by {
                if k < i {
                    assert(r[k] == prev[k]);
                    assert(hashes@.subrange(32 * k, 32 * k + 32) =~= old_hashes.subrange(32 * k, 32 * k + 32));
                } else {
                    assert(hashes@.subrange(32 * k, 32 * k + 32) =~= block.hash@);
                }
            }
            assert(lanes(r, numbers@, hashes@));
        }
    }
    (numbers, hashes)
}

/// Splits a cursor into its envelope flag and fields.
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == cursor_lanes(cursor)))]
fn cursor_fields(cursor: Option<Position>) -> (u8, u64, u64) {
    match cursor {
        Some(pos) => (1, pos.block, pos.log_index),
        None => (0, 0, 0),
    }
}

/// Builds one envelope from fold state, cursor, and the ring's oldest `len` entries.
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    requires
        ring.wf(),
        len <= ring@.len(),
    ensures
        encodes::<F, _>(r, cursor, ring@.subrange(0, len as int)),
))]
fn envelope<F: Persist>(
    fold: &F,
    cursor: Option<Position>,
    ring: &BlockRing,
    len: usize,
) -> Envelope<&'static [u8]> {
    let (ring_numbers, ring_hashes) = ring_lanes(ring, len);
    let (cursor_set, cursor_block, cursor_log_index) = cursor_fields(cursor);
    let mut state = Vec::new();
    fold.encode_state(&mut state);
    Envelope {
        magic: SNAPSHOT_MAGIC,
        version: SNAPSHOT_VERSION,
        tag: F::STATE_TAG.as_bytes(),
        cursor_set,
        cursor_block,
        cursor_log_index,
        ring_numbers,
        ring_hashes,
        state,
    }
}

/// Errors from encoding or decoding a snapshot envelope.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, PartialEq, Eq)]
pub enum SnapshotError<E> {
    /// Input is shorter than magic, version, and trailer together.
    TooShort,
    /// Leading bytes are not `SNAPSHOT_MAGIC`.
    BadMagic,
    /// Wire format version differs from `SNAPSHOT_VERSION`.
    BadVersion {
        /// Version read from the input.
        got: u16,
    },
    /// State tag differs from the fold's `STATE_TAG`.
    BadTag,
    /// Trailer checksum disagrees with the payload.
    Crc {
        /// Checksum stored in the trailer.
        expected: u32,
        /// Checksum recomputed over the payload.
        got: u32,
    },
    /// Payload does not decode as an envelope.
    Envelope,
    /// An envelope field exceeds the engine-owned length ceiling.
    TooLarge {
        /// Longest field length the codec accepts, in bytes.
        limit: usize,
    },
    /// Stored ring holds more entries than the configured capacity.
    RingExceedsCapacity {
        /// Entries the stored ring holds.
        len: usize,
        /// Entries the configuration allows.
        capacity: usize,
    },
    /// Stored ring block numbers are not strictly ascending.
    RingNotAscending,
    /// Stored hash bytes do not match the ring entry count.
    RingHashLenMismatch,
    /// Stored ring's newest block differs from the stored cursor block, or a
    /// cursorless snapshot carries ring entries.
    RingCursorMismatch,
    /// Caller configuration is invalid.
    Config(ConfigError),
    /// Fold refused its own state bytes.
    State(E),
}

impl<E: fmt::Display> fmt::Display for SnapshotError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooShort => {
                write!(f, "snapshot is shorter than the minimum envelope size")
            }
            Self::BadMagic => write!(f, "snapshot magic bytes do not match"),
            Self::BadVersion { got } => {
                write!(f, "snapshot version {got} is unsupported")
            }
            Self::BadTag => write!(f, "snapshot state tag does not match the fold's tag"),
            Self::Crc { expected, got } => {
                write!(
                    f,
                    "snapshot crc mismatch: expected {expected:#010x}, got {got:#010x}"
                )
            }
            Self::Envelope => write!(f, "snapshot envelope failed to decode"),
            Self::TooLarge { limit } => {
                write!(f, "snapshot envelope field exceeds the {limit} byte limit")
            }
            Self::RingExceedsCapacity { len, capacity } => {
                write!(
                    f,
                    "snapshot ring holds {len} entries, exceeding capacity {capacity}"
                )
            }
            Self::RingNotAscending => {
                write!(f, "snapshot ring block numbers are not strictly ascending")
            }
            Self::RingHashLenMismatch => {
                write!(
                    f,
                    "snapshot ring hash bytes do not match the number of ring entries"
                )
            }
            Self::RingCursorMismatch => {
                write!(
                    f,
                    "snapshot ring does not end at the cursor block, or has entries without a cursor"
                )
            }
            Self::Config(error) => write!(f, "snapshot config invalid: {error}"),
            Self::State(error) => write!(f, "snapshot state failed to decode: {error}"),
        }
    }
}

impl<E: fmt::Debug + fmt::Display> core::error::Error for SnapshotError<E> {}

#[cfg_attr(docsrs, doc(cfg(feature = "wincode")))]
#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl<F: Persist> Engine<F> {
    /// Appends the framed envelope: wincode payload plus a CRC32C trailer.
    ///
    /// Fails with `TooLarge` when a field exceeds the engine-owned length ceiling,
    /// leaving `out` as it found it.
    // The envelope is `encodes(_, self@.cursor, self@.ring)` (`envelope`'s ensures).
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            self.wf(),
    ))]
    pub fn encode_snapshot(
        &self,
        out: &mut Vec<u8>,
    ) -> Result<(), SnapshotError<F::PersistError>> {
        let ring = self.ring();
        write_envelope(&envelope(self.fold(), self.cursor(), ring, ring.len()), out)
    }

    /// Encodes the oldest live checkpoint; Ok(None) means nothing is live and nothing
    /// was appended.
    ///
    /// The returned point is the encoded snapshot's cursor, trailing the live cursor by
    /// the checkpoint span.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            r matches Ok(Some(p)) ==> self@.durable_point() == Some(p),
            r matches Ok(None) <==> self@.durable_point() is None,
    ))]
    pub fn encode_durable_snapshot(
        &self,
        out: &mut Vec<u8>,
    ) -> Result<Option<Position>, SnapshotError<F::PersistError>> {
        let Some((envelope, point)) = self.durable_envelope() else {
            return Ok(None);
        };
        match write_envelope(&envelope, out) {
            Ok(()) => Ok(Some(point)),
            Err(error) => Err(error),
        }
    }

    /// The durable snapshot's envelope and point: the oldest live slot's fold and
    /// cursor, and the ring entries at or below the cursor block.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            self.wf(),
        ensures
            match r {
                None => self@.durable_point() is None,
                Some((e, p)) => self@.durable_point() == Some(p) && durable_encodes::<F, _>(self@, e),
            },
    ))]
    fn durable_envelope(&self) -> Option<(Envelope<&'static [u8]>, Position)> {
        let slot = self.oldest_checkpoint()?;
        #[cfg(verus_keep_ghost)]
        proof! {
            slot.lemma_view();
        }
        let point = slot.cursor?;
        let ring = self.ring();
        let len = ring.len_at_or_below(point.block);
        Some((envelope(&slot.fold, slot.cursor, ring, len), point))
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "wincode")))]
#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl<F: Persist> Engine<F> {
    /// Rebuilds an engine from an envelope; checkpoints, skips, freshness start empty.
    // Any bytes that decode give a `wf` engine, with no trust in the codec or the
    // checksum (both have empty contracts in tcb.rs). Every `Err` path is panic-free.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            r matches Ok(e) ==> e.wf() && restored(e@, config),
    ))]
    pub fn decode_snapshot(
        bytes: &[u8],
        config: EngineConfig,
    ) -> Result<Self, SnapshotError<F::PersistError>> {
        if let Err(error) = config.validate() {
            return Err(SnapshotError::Config(error));
        }
        if bytes.len() < MIN_ENVELOPE_LEN {
            return Err(SnapshotError::TooShort);
        }
        if bytes[..MAGIC_LEN] != SNAPSHOT_MAGIC {
            return Err(SnapshotError::BadMagic);
        }
        let version =
            u16::from(bytes[MAGIC_LEN]) | (u16::from(bytes[MAGIC_LEN + 1]) << 8);
        if version != SNAPSHOT_VERSION {
            return Err(SnapshotError::BadVersion { got: version });
        }

        let Some((payload, trailer)) = bytes.split_last_chunk::<CRC_LEN>() else {
            return Err(SnapshotError::TooShort);
        };
        let expected_crc = u32::from(trailer[0])
            | (u32::from(trailer[1]) << 8)
            | (u32::from(trailer[2]) << 16)
            | (u32::from(trailer[3]) << 24);
        let computed_crc = crc32c(payload);
        if computed_crc != expected_crc {
            return Err(SnapshotError::Crc {
                expected: expected_crc,
                got: computed_crc,
            });
        }

        let envelope = match read_envelope(payload) {
            Ok(envelope) => envelope,
            Err(_error) => return Err(SnapshotError::Envelope),
        };
        Self::from_envelope(envelope, config)
    }

    /// Checks a decoded envelope's fields and rebuilds the engine they describe.
    // The round trip (`lemma_envelope_round_trip`): an envelope `encodes` built passes
    // every check here, and the engine returned has its cursor and ring.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires
            config.valid(),
        ensures
            r matches Ok(e) ==> e.wf() && restored(e@, config) && decoded(e@, envelope),
            accepted::<F, _>(envelope, config) ==> r is Ok || r matches Err(SnapshotError::State(_)),
    ))]
    fn from_envelope(
        envelope: Envelope<Vec<u8>>,
        config: EngineConfig,
    ) -> Result<Self, SnapshotError<F::PersistError>> {
        if envelope.tag.as_slice() != F::STATE_TAG.as_bytes() {
            return Err(SnapshotError::BadTag);
        }

        if envelope.ring_numbers.len() > config.ring_capacity {
            return Err(SnapshotError::RingExceedsCapacity {
                len: envelope.ring_numbers.len(),
                capacity: config.ring_capacity,
            });
        }
        if first_descent(&envelope.ring_numbers).is_some() {
            return Err(SnapshotError::RingNotAscending);
        }
        // The capacity check above bounds the count, so the product cannot overflow;
        // saturation would still fail the comparison.
        if envelope.ring_hashes.len()
            != envelope.ring_numbers.len().saturating_mul(HASH_LEN)
        {
            return Err(SnapshotError::RingHashLenMismatch);
        }
        let cursor = if envelope.cursor_set != 0 {
            Some(Position::new(
                envelope.cursor_block,
                envelope.cursor_log_index,
            ))
        } else {
            None
        };
        // A cursorless engine has an empty ring, so None must pair with no entries.
        let tip_matches = match (envelope.ring_numbers.last(), cursor) {
            (Some(&tip), Some(pos)) => tip == pos.block,
            (None, None) => true,
            _ => false,
        };
        if !tip_matches {
            return Err(SnapshotError::RingCursorMismatch);
        }

        let fold = match F::decode_state(&envelope.state) {
            Ok(fold) => fold,
            Err(error) => return Err(SnapshotError::State(error)),
        };

        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost numbers = envelope.ring_numbers@;
            let ghost hashes = envelope.ring_hashes@;
            broadcast use vstd::laws_cmp::group_laws_cmp;
            lemma_ascending_pairwise(numbers);
            assert(hashes.len() == numbers.len() * HASH_LEN);
        }
        let mut ring = BlockRing::with_capacity(config.ring_capacity);
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                ring.wf(),
                ring.cap() == config.ring_capacity,
                numbers == envelope.ring_numbers@,
                hashes == envelope.ring_hashes@,
                numbers.len() <= config.ring_capacity <= 0x10_0000,
                hashes.len() == numbers.len() * HASH_LEN,
                forall|a: int, b: int|
                    #![trigger numbers[a], numbers[b]]
                    0 <= a < b < numbers.len() ==> numbers[a] < numbers[b],
                ring_from_lanes(ring@, numbers, hashes, i as int),
        ))]
        for i in 0..envelope.ring_numbers.len() {
            let mut hash = [0u8; HASH_LEN];
            hash.copy_from_slice(&envelope.ring_hashes[i * HASH_LEN..(i + 1) * HASH_LEN]);
            #[cfg(verus_keep_ghost)]
            proof! {
                if i > 0 {
                    assert(ring@.last().number == numbers[i - 1]);
                    assert(numbers[i - 1] < numbers[i as int]);
                }
            }
            ring.push(BlockRef {
                number: envelope.ring_numbers[i],
                hash,
            });
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(ring_ascending(ring@));
        }

        let mut engine = match Engine::new(fold, config) {
            Ok(engine) => engine,
            Err(error) => return Err(SnapshotError::Config(error)),
        };
        engine.restore_cursor_and_ring(cursor, ring);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(from_lanes(
                engine@,
                envelope.cursor_set,
                envelope.cursor_block,
                envelope.cursor_log_index,
                numbers,
                hashes,
            ));
        }
        Ok(engine)
    }
}

#[cfg(verus_keep_ghost)]
verus! {

/// Ring entries `0..len` are the envelope lanes: `numbers[k]` with hash bytes
/// `hashes[32k..32k + 32]`.
pub open spec fn ring_from_lanes(ring: Seq<BlockRef>, numbers: Seq<u64>, hashes: Seq<u8>, len: int) -> bool {
    &&& ring.len() == len
    &&& forall|k: int|
        #![trigger ring[k]]
        0 <= k < len ==> ring[k].number == numbers[k]
            && ring[k].hash@ == hashes.subrange(32 * k, 32 * k + 32)
}

/// `v`'s cursor and ring are the ones an envelope with these fields describes.
pub open spec fn from_lanes(
    v: EngineView,
    cursor_set: u8,
    cursor_block: u64,
    cursor_log_index: u64,
    numbers: Seq<u64>,
    hashes: Seq<u8>,
) -> bool {
    &&& v.cursor == if cursor_set != 0 {
        Some(Position { block: cursor_block, log_index: cursor_log_index })
    } else {
        None
    }
    &&& hashes.len() == 32 * numbers.len()
    &&& ring_from_lanes(v.ring, numbers, hashes, numbers.len() as int)
}

/// What `decode_snapshot` returns. Nothing but the fold, cursor and
/// ring comes from the bytes; the cursor and ring are some envelope's fields, and the
/// ring fits the configured window.
pub open spec fn restored(v: EngineView, config: EngineConfig) -> bool {
    &&& v.status == EngineStatus::Active
    &&& v.last_verified is None
    &&& v.skips == 0
    &&& v.resets == 0
    &&& v.slots == Seq::new(config.checkpoint_slots as nat, |_i: int| None::<SlotView>)
    &&& v.ring.len() <= config.ring_capacity
    &&& exists|cursor_set: u8, cursor_block: u64, cursor_log_index: u64, numbers: Seq<u64>, hashes: Seq<u8>|
        from_lanes(v, cursor_set, cursor_block, cursor_log_index, numbers, hashes)
}


/// `numbers` and `hashes` are the envelope lanes of `ring`: one number and 32 hash bytes
/// per entry.
spec fn lanes(ring: Seq<BlockRef>, numbers: Seq<u64>, hashes: Seq<u8>) -> bool {
    &&& numbers.len() == ring.len()
    &&& hashes.len() == 32 * ring.len()
    &&& ring_from_lanes(ring, numbers, hashes, ring.len() as int)
}

/// The envelope flag and fields of a cursor.
spec fn cursor_lanes(cursor: Option<Position>) -> (u8, u64, u64) {
    match cursor {
        Some(p) => (1u8, p.block, p.log_index),
        None => (0u8, 0u64, 0u64),
    }
}

/// `e` is the envelope encode builds for `cursor` and `ring`. Its state bytes are the
/// fold's own encoding, which is trusted.
spec fn encodes<F: Persist, T: View<V = Seq<u8>>>(e: Envelope<T>, cursor: Option<Position>, ring: Seq<BlockRef>) -> bool {
    &&& e.magic == SNAPSHOT_MAGIC
    &&& e.version == SNAPSHOT_VERSION
    &&& e.tag@ == F::STATE_TAG.spec_bytes()
    &&& (e.cursor_set, e.cursor_block, e.cursor_log_index) == cursor_lanes(cursor)
    &&& lanes(ring, e.ring_numbers@, e.ring_hashes@)
}

/// `e` encodes `v`'s durable snapshot: the durable point, and the ring prefix at or
/// below its block, whose length is the lane length.
spec fn durable_encodes<F: Persist, T: View<V = Seq<u8>>>(v: EngineView, e: Envelope<T>) -> bool {
    let k = e.ring_numbers@.len() as int;
    &&& v.durable_point() is Some
    &&& prefix_at_or_below(v.ring, v.durable_point().unwrap().block, k)
    &&& encodes::<F, _>(e, v.durable_snapshot(k, 0).cursor, v.durable_snapshot(k, 0).ring)
}

/// The envelope fields `from_envelope` accepts, bar the state bytes.
spec fn accepted<F: Persist, T: View<V = Seq<u8>>>(e: Envelope<T>, config: EngineConfig) -> bool {
    let n = e.ring_numbers@;
    &&& e.tag@ == F::STATE_TAG.spec_bytes()
    &&& n.len() <= config.ring_capacity
    &&& forall|a: int, b: int| #![trigger n[a], n[b]] 0 <= a < b < n.len() ==> n[a] < n[b]
    &&& e.ring_hashes@.len() == 32 * n.len()
    &&& if e.cursor_set != 0 {
        n.len() > 0 && n.last() == e.cursor_block
    } else {
        n.len() == 0
    }
}

/// `v`'s cursor and ring are the ones envelope `e` describes.
spec fn decoded<T>(v: EngineView, e: Envelope<T>) -> bool {
    from_lanes(v, e.cursor_set, e.cursor_block, e.cursor_log_index, e.ring_numbers@, e.ring_hashes@)
}

/// Round trip at the envelope level: the envelope encode builds for an ascending ring
/// that ends at the cursor block passes `from_envelope`'s checks, and every engine it
/// decodes to has that cursor and ring.
proof fn lemma_envelope_round_trip<F: Persist, T: View<V = Seq<u8>>>(
    e: Envelope<T>,
    cursor: Option<Position>,
    ring: Seq<BlockRef>,
    config: EngineConfig,
)
    requires
        encodes::<F, _>(e, cursor, ring),
        ring_ascending(ring),
        match cursor {
            Some(c) => ring.len() > 0 && ring.last().number == c.block,
            None => ring.len() == 0,
        },
        ring.len() <= config.ring_capacity,
    ensures
        accepted::<F, _>(e, config),
        forall|v: EngineView| #[trigger] decoded(v, e) ==> v.cursor == cursor && v.ring == ring,
{
    let n = e.ring_numbers@;
    assert forall|a: int, b: int| 0 <= a < b < n.len() implies #[trigger] n[a] < #[trigger] n[b] by {
        assert(ring[a].number < ring[b].number);
    }
    if cursor is Some {
        assert(n.last() == ring[ring.len() - 1].number);
    }
    assert forall|v: EngineView| #[trigger] decoded(v, e) implies v.cursor == cursor && v.ring == ring by {
        assert forall|k: int| 0 <= k < ring.len() implies v.ring[k] == ring[k] by {
            assert(v.ring[k].hash@ == ring[k].hash@);
            assert(v.ring[k].hash =~= ring[k].hash);
        }
        assert(v.ring =~= ring);
    }
}

/// Round trip: decoding the envelope `encode_durable_snapshot` builds gives back the
/// durable snapshot's view, bar the fold, for a config whose window holds the ring.
proof fn lemma_durable_round_trip<F: Persist, T: View<V = Seq<u8>>>(v: EngineView, e: Envelope<T>, config: EngineConfig)
    requires
        v.wf(),
        durable_encodes::<F, _>(v, e),
        v.ring.len() <= config.ring_capacity,
    ensures
        accepted::<F, _>(e, config),
        forall|d: EngineView|
            restored(d, config) && #[trigger] decoded(d, e) ==> d == (EngineView {
                fold: d.fold,
                ..v.durable_snapshot(e.ring_numbers@.len() as int, config.checkpoint_slots as nat)
            }),
{
    let k = e.ring_numbers@.len() as int;
    lemma_durable_snapshot(v, k, 0);
    let snap = v.durable_snapshot(k, 0);
    lemma_envelope_round_trip::<F, _>(e, snap.cursor, snap.ring, config);
    let full = v.durable_snapshot(k, config.checkpoint_slots as nat);
    assert forall|d: EngineView| restored(d, config) && #[trigger] decoded(d, e) implies d == (
    EngineView { fold: d.fold, ..full }) by {
        assert(d.slots =~= full.slots);
    }
}

} // verus!

/// Hand-builds and frames an envelope with caller-chosen fields, for adversarial tests.
#[cfg(test)]
fn encode_custom(
    tag: &'static [u8],
    cursor: Option<Position>,
    ring: &[BlockRef],
    state: Vec<u8>,
) -> Vec<u8> {
    let ring_numbers = ring.iter().map(|block| block.number).collect();
    let ring_hashes = ring.iter().flat_map(|block| block.hash).collect();
    let (cursor_set, cursor_block, cursor_log_index) = cursor_fields(cursor);
    let envelope = Envelope {
        magic: SNAPSHOT_MAGIC,
        version: SNAPSHOT_VERSION,
        tag,
        cursor_set,
        cursor_block,
        cursor_log_index,
        ring_numbers,
        ring_hashes,
        state,
    };
    let mut out = Vec::new();
    write_envelope::<()>(&envelope, &mut out).expect("test envelope fits the limit");
    out
}

#[cfg(test)]
mod tests {
    use super::{
        SNAPSHOT_MAGIC,
        SNAPSHOT_VERSION,
        SnapshotError,
        crc32c,
        encode_custom,
    };
    use crate::{
        batch::Batch,
        engine::{
            Engine,
            EngineConfig,
        },
        error::ConfigError,
        position::{
            BlockRef,
            Position,
        },
        snapshot::Persist,
        test_util::RecordingFold,
    };
    #[cfg(not(feature = "std"))]
    use alloc::{
        vec,
        vec::Vec,
    };
    #[cfg(feature = "std")]
    use std::{
        vec,
        vec::Vec,
    };

    const CRC_LEN: usize = 4;

    fn block(number: u64, salt: u8) -> BlockRef {
        let mut hash = [0u8; 32];
        hash[..8].copy_from_slice(&number.to_le_bytes());
        hash[8] = salt;
        BlockRef { number, hash }
    }

    fn test_config() -> EngineConfig {
        EngineConfig {
            ring_capacity: 8,
            checkpoint_slots: 0,
        }
    }

    fn batch_of(
        boundary: Option<BlockRef>,
        spans: Vec<(BlockRef, Vec<u32>)>,
    ) -> Batch<u64> {
        let mut batch = Batch::new();
        batch.boundary = boundary;
        for (block, log_indices) in spans {
            batch.push_block(
                block,
                log_indices
                    .into_iter()
                    .map(|index| (index, u64::from(index))),
            );
        }
        batch
    }

    fn test_engine() -> Engine<RecordingFold> {
        Engine::new(RecordingFold::default(), test_config()).unwrap()
    }

    fn checkpointed_config(slots: usize) -> EngineConfig {
        EngineConfig {
            ring_capacity: 8,
            checkpoint_slots: slots,
        }
    }

    /// Engine checkpointed at block 2, then folded on to block 4.
    fn engine_checkpointed_at_block_two() -> Engine<RecordingFold> {
        let mut engine =
            Engine::new(RecordingFold::default(), checkpointed_config(2)).unwrap();
        engine
            .apply_batch(&batch_of(
                None,
                vec![(block(1, 0), vec![0]), (block(2, 0), vec![0])],
            ))
            .unwrap();
        engine
    }

    fn fold_on_to_block_four(engine: &mut Engine<RecordingFold>) {
        engine
            .apply_batch(&batch_of(
                Some(block(2, 0)),
                vec![(block(3, 0), vec![0]), (block(4, 0), vec![0])],
            ))
            .unwrap();
    }

    #[test]
    fn crc32c_matches_the_iscsi_check_value() {
        // given the check input the CRC catalogue publishes for CRC-32/ISCSI
        let input = b"123456789";
        // when the configured backend hashes it
        let sum = crc32c(input);
        // then it is the published check value, so both backends frame the same bytes
        assert_eq!(sum, 0xe306_9283);
    }

    #[test]
    fn encode_durable_snapshot_matches_a_snapshot_of_the_checkpointed_engine() {
        // given a snapshot captured at the block 2 checkpoint, then folding on to block 4
        let mut engine = engine_checkpointed_at_block_two();
        engine.checkpoint();
        let mut at_checkpoint = Vec::new();
        engine.encode_snapshot(&mut at_checkpoint).unwrap();
        fold_on_to_block_four(&mut engine);
        // when the durable snapshot encodes
        let mut durable = Vec::new();
        let point = engine.encode_durable_snapshot(&mut durable).unwrap();
        // then the bytes are identical and the point is the checkpoint's cursor
        assert_eq!(durable, at_checkpoint);
        assert_eq!(point, Some(Position::new(2, 0)));
    }

    #[test]
    fn encode_durable_snapshot_without_checkpoints_appends_nothing() {
        // given an engine with no retained slots and one whose oldest slot has no cursor
        let empty = test_engine();
        let mut cursorless =
            Engine::new(RecordingFold::default(), checkpointed_config(2)).unwrap();
        cursorless.checkpoint();
        // when both encode into the same buffer
        let mut out = Vec::new();
        let empty_point = empty.encode_durable_snapshot(&mut out).unwrap();
        let cursorless_point = cursorless.encode_durable_snapshot(&mut out).unwrap();
        // then both report Ok(None) and the buffer is still empty
        assert_eq!(empty_point, None);
        assert_eq!(cursorless_point, None);
        assert!(out.is_empty());
    }

    #[test]
    fn durable_snapshot_round_trips_through_decode() {
        // given a durable snapshot taken at the block 2 checkpoint after folding to block 4
        let mut engine = engine_checkpointed_at_block_two();
        engine.checkpoint();
        let checkpoint_view = engine.fold().applied.clone();
        let checkpoint_ring: Vec<BlockRef> = engine.observed().collect();
        fold_on_to_block_four(&mut engine);
        let mut durable = Vec::new();
        engine.encode_durable_snapshot(&mut durable).unwrap();
        // when decoded with the same config
        let decoded =
            Engine::<RecordingFold>::decode_snapshot(&durable, checkpointed_config(2))
                .unwrap();
        // then cursor, view, and observed ring equal the checkpoint-time state
        assert_eq!(decoded.cursor(), Some(Position::new(2, 0)));
        assert_eq!(decoded.fold().applied, checkpoint_view);
        assert_eq!(decoded.observed().collect::<Vec<_>>(), checkpoint_ring);
    }

    #[test]
    fn envelope_layout_pins_magic_and_version_offsets() {
        // given an encoded snapshot of a fresh engine
        let engine = test_engine();
        let mut bytes = Vec::new();
        engine.encode_snapshot(&mut bytes).unwrap();
        // when reading the fixed header offsets
        let magic = &bytes[0..8];
        let version = u16::from_le_bytes([bytes[8], bytes[9]]);
        // then bytes 0..8 equal SNAPSHOT_MAGIC and bytes 8..10 equal the version LE
        assert_eq!(magic, SNAPSHOT_MAGIC);
        assert_eq!(version, SNAPSHOT_VERSION);
    }

    #[test]
    fn borrowed_and_owned_tags_serialize_to_the_same_bytes() {
        // given one envelope with the encode side's borrowed tag and one with the decode
        // side's owned tag, equal in every field
        let tag = RecordingFold::STATE_TAG.as_bytes();
        let borrowed = super::Envelope {
            magic: SNAPSHOT_MAGIC,
            version: SNAPSHOT_VERSION,
            tag,
            cursor_set: 1,
            cursor_block: 7,
            cursor_log_index: 3,
            ring_numbers: vec![6, 7],
            ring_hashes: vec![9; 64],
            state: vec![1, 2, 3],
        };
        let owned = super::Envelope {
            magic: SNAPSHOT_MAGIC,
            version: SNAPSHOT_VERSION,
            tag: tag.to_vec(),
            cursor_set: 1,
            cursor_block: 7,
            cursor_log_index: 3,
            ring_numbers: vec![6, 7],
            ring_hashes: vec![9; 64],
            state: vec![1, 2, 3],
        };
        // when both are serialized with the envelope config
        let mut from_borrowed = Vec::new();
        assert!(super::write_payload(&mut from_borrowed, &borrowed));
        let mut from_owned = Vec::new();
        wincode::config::serialize_into(&mut from_owned, &owned, super::ENVELOPE_CONFIG)
            .unwrap();
        // then the bytes are equal, and they decode to the same tag
        assert_eq!(from_borrowed, from_owned);
        let decoded = super::read_envelope(&from_borrowed).unwrap();
        assert_eq!(decoded.tag, tag);
    }

    #[test]
    fn encode_decode_round_trips_cursor_ring_and_state() {
        // given an engine with applied events across two blocks
        let mut engine = test_engine();
        engine
            .apply_batch(&batch_of(
                None,
                vec![(block(1, 0), vec![0, 1]), (block(2, 0), vec![0])],
            ))
            .unwrap();
        let mut encoded = Vec::new();
        // when encoded and decoded with the same config
        engine.encode_snapshot(&mut encoded).unwrap();
        let decoded =
            Engine::<RecordingFold>::decode_snapshot(&encoded, test_config()).unwrap();
        // then cursor, observed ring, and view all match and a re-encode is byte-identical
        assert_eq!(decoded.cursor(), engine.cursor());
        assert_eq!(
            decoded.observed().collect::<Vec<_>>(),
            engine.observed().collect::<Vec<_>>()
        );
        assert_eq!(decoded.fold().applied, engine.fold().applied);
        let mut re_encoded = Vec::new();
        decoded.encode_snapshot(&mut re_encoded).unwrap();
        assert_eq!(re_encoded, encoded);
    }

    #[test]
    fn empty_engine_round_trips() {
        // given a fresh engine
        let engine = test_engine();
        let mut encoded = Vec::new();
        // when encoded and decoded
        engine.encode_snapshot(&mut encoded).unwrap();
        let decoded =
            Engine::<RecordingFold>::decode_snapshot(&encoded, test_config()).unwrap();
        // then cursor None and empty ring
        assert_eq!(decoded.cursor(), None);
        assert_eq!(decoded.observed().len(), 0);
    }

    #[test]
    fn state_far_above_the_codec_default_limit_round_trips() {
        // given a fold state of 200_000 entries, well past a 4 MiB field
        const ENTRIES: u64 = 200_000;
        let applied = (0..ENTRIES)
            .map(|index| (Position::new(index + 1, 0), index))
            .collect::<Vec<_>>();
        let fold = RecordingFold {
            applied,
            fail_at: None,
        };
        let engine = Engine::new(fold, test_config()).unwrap();
        let mut encoded = Vec::new();
        // when encoded and decoded
        engine.encode_snapshot(&mut encoded).unwrap();
        let decoded =
            Engine::<RecordingFold>::decode_snapshot(&encoded, test_config()).unwrap();
        // then the payload exceeds 4 MiB and the view survives the round trip
        assert!(encoded.len() > 4 << 20);
        assert_eq!(decoded.fold().applied, engine.fold().applied);
    }

    #[test]
    fn invalid_config_is_refused_before_any_ring_allocation() {
        // given a valid envelope and a ring capacity that is not a power of two
        let engine = test_engine();
        let mut encoded = Vec::new();
        engine.encode_snapshot(&mut encoded).unwrap();
        let bad_config = EngineConfig {
            ring_capacity: 12,
            checkpoint_slots: 0,
        };
        // when decoded with it
        let result = Engine::<RecordingFold>::decode_snapshot(&encoded, bad_config);
        // then Config carries the typed capacity error, never a debug assertion
        assert_eq!(
            result.unwrap_err(),
            SnapshotError::Config(ConfigError::RingCapacityNotPowerOfTwo { got: 12 })
        );
    }

    #[test]
    fn oversized_slot_count_is_refused_before_any_slot_allocation() {
        // given a valid envelope and a slot count whose vector would overflow
        let engine = test_engine();
        let mut encoded = Vec::new();
        engine.encode_snapshot(&mut encoded).unwrap();
        let bad_config = EngineConfig {
            ring_capacity: 8,
            checkpoint_slots: usize::MAX,
        };
        // when decoded with it
        let result = Engine::<RecordingFold>::decode_snapshot(&encoded, bad_config);
        // then Config carries the typed slot error, never a capacity-overflow panic
        assert_eq!(
            result.unwrap_err(),
            SnapshotError::Config(ConfigError::CheckpointSlotsOutOfRange {
                got: usize::MAX
            })
        );
    }

    #[test]
    fn wrong_tag_is_refused_before_state_decode() {
        // given an envelope encoded for a fold with a different STATE_TAG
        let bytes = encode_custom(b"some-other-fold-tag", None, &[], Vec::new());
        // when decoded
        let result = Engine::<RecordingFold>::decode_snapshot(&bytes, test_config());
        // then BadTag
        assert_eq!(result.unwrap_err(), SnapshotError::BadTag);
    }

    #[test]
    fn flipped_bit_fails_crc() {
        // given an encoded snapshot with one bit flipped in the payload
        let engine = test_engine();
        let mut bytes = Vec::new();
        engine.encode_snapshot(&mut bytes).unwrap();
        bytes[10] ^= 0x01;
        // when decoded
        let result = Engine::<RecordingFold>::decode_snapshot(&bytes, test_config());
        // then Crc
        assert!(matches!(result, Err(SnapshotError::Crc { .. })));
    }

    #[test]
    fn truncated_envelope_is_too_short_or_crc() {
        // given prefixes of every length below the full encoding
        let engine = test_engine();
        let mut encoded = Vec::new();
        engine.encode_snapshot(&mut encoded).unwrap();
        // when decoded
        for len in 0..encoded.len() {
            let result =
                Engine::<RecordingFold>::decode_snapshot(&encoded[..len], test_config());
            // then every result is a typed error, never a panic
            assert!(result.is_err());
        }
    }

    #[test]
    fn ring_larger_than_capacity_is_refused() {
        // given an envelope from ring capacity 16
        let wide_config = EngineConfig {
            ring_capacity: 16,
            checkpoint_slots: 0,
        };
        let mut engine = Engine::new(RecordingFold::default(), wide_config).unwrap();
        let mut boundary = None;
        for number in 1..=9u64 {
            engine
                .apply_batch(&batch_of(boundary, vec![(block(number, 0), vec![0])]))
                .unwrap();
            boundary = Some(block(number, 0));
        }
        let mut encoded = Vec::new();
        engine.encode_snapshot(&mut encoded).unwrap();
        // when decoded with capacity 8 config
        let narrow_config = EngineConfig {
            ring_capacity: 8,
            checkpoint_slots: 0,
        };
        let result = Engine::<RecordingFold>::decode_snapshot(&encoded, narrow_config);
        // then RingExceedsCapacity
        assert_eq!(
            result.unwrap_err(),
            SnapshotError::RingExceedsCapacity {
                len: 9,
                capacity: 8
            }
        );
    }

    #[test]
    fn corrupt_length_rejects_at_crc_before_decode() {
        // given the state length field corrupted to a huge value, trailer left stale
        let engine = test_engine();
        let mut encoded = Vec::new();
        engine.encode_snapshot(&mut encoded).unwrap();
        let mut state_bytes = Vec::new();
        engine.fold().encode_state(&mut state_bytes);
        let state_len_prefix_start = encoded.len() - CRC_LEN - state_bytes.len() - 8;
        encoded[state_len_prefix_start..state_len_prefix_start + 8]
            .copy_from_slice(&u64::MAX.to_le_bytes());
        // when decoded
        let result = Engine::<RecordingFold>::decode_snapshot(&encoded, test_config());
        // then the error is Crc; length-driven preallocation is unreachable behind the checksum
        assert!(matches!(result, Err(SnapshotError::Crc { .. })));
    }

    #[test]
    fn cursor_ring_mismatch_is_refused() {
        // given a hand-built envelope whose newest ring number differs from the cursor block
        let mut state = Vec::new();
        RecordingFold::default().encode_state(&mut state);
        let bytes = encode_custom(
            RecordingFold::STATE_TAG.as_bytes(),
            Some(Position::new(5, 0)),
            &[block(3, 0)],
            state,
        );
        // when decoded
        let result = Engine::<RecordingFold>::decode_snapshot(&bytes, test_config());
        // then RingCursorMismatch
        assert_eq!(result.unwrap_err(), SnapshotError::RingCursorMismatch);
    }

    #[test]
    fn cursorless_envelope_with_a_ring_is_refused() {
        // given a hand-built envelope with no cursor but one observed block
        let mut state = Vec::new();
        RecordingFold::default().encode_state(&mut state);
        let bytes = encode_custom(
            RecordingFold::STATE_TAG.as_bytes(),
            None,
            &[block(5, 0)],
            state,
        );
        // when decoded
        let result = Engine::<RecordingFold>::decode_snapshot(&bytes, test_config());
        // then RingCursorMismatch; no engine reaches a cursorless state with a ring
        assert_eq!(result.unwrap_err(), SnapshotError::RingCursorMismatch);
    }
}
