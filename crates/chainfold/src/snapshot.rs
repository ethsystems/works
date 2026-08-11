//! Engine-owned snapshot envelope: canonical bytes framed with a CRC32C trailer.

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use core::fmt;

use crate::{
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
const MAX_ENVELOPE_FIELD_LEN: usize = 1 << 30;

/// Codec settings of record: fixint little-endian with the engine-owned length ceiling.
type EnvelopeConfig = wincode::config::Configuration<true, MAX_ENVELOPE_FIELD_LEN>;

/// Codec instance the encode and decode paths share.
const ENVELOPE_CONFIG: EnvelopeConfig = EnvelopeConfig::new();

/// Byte length of a `BlockRef` hash.
const HASH_LEN: usize = 32;
/// Byte length of the magic prefix.
const MAGIC_LEN: usize = 8;
/// Byte length of the version field.
const VERSION_LEN: usize = 2;
/// Byte length of the CRC32C trailer.
const CRC_LEN: usize = 4;
/// Smallest possible encoded snapshot: magic, version, and trailer with an empty payload.
const MIN_ENVELOPE_LEN: usize = MAGIC_LEN + VERSION_LEN + CRC_LEN;

/// Fixed 8-byte prefix identifying a chainfold snapshot.
pub const SNAPSHOT_MAGIC: [u8; 8] = *b"CHNFOLD1";
/// Snapshot envelope wire format version.
pub const SNAPSHOT_VERSION: u16 = 1;

/// Fold state with a canonical byte encoding and an identity tag.
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

#[derive(Debug, wincode::SchemaWrite, wincode::SchemaRead)]
struct Envelope {
    magic: [u8; 8],
    version: u16,
    tag: Vec<u8>,
    cursor_set: u8,
    cursor_block: u64,
    cursor_log_index: u64,
    ring_numbers: Vec<u64>,
    ring_hashes: Vec<u8>,
    state: Vec<u8>,
}

/// Serializes an envelope and appends its CRC32C trailer.
///
/// The codec refuses a field longer than `MAX_ENVELOPE_FIELD_LEN`, which is the only
/// way a fixed-shape envelope fails to serialize into a growable buffer.
fn write_envelope<E>(
    envelope: &Envelope,
    out: &mut Vec<u8>,
) -> Result<(), SnapshotError<E>> {
    let start = out.len();
    if wincode::config::serialize_into(&mut *out, envelope, ENVELOPE_CONFIG).is_err() {
        out.truncate(start);
        return Err(SnapshotError::TooLarge {
            limit: MAX_ENVELOPE_FIELD_LEN,
        });
    }
    let crc = crc32c(&out[start..]);
    out.extend_from_slice(&crc.to_le_bytes());
    Ok(())
}

/// Builds the ring lanes of an envelope from a block sequence.
fn ring_lanes(blocks: impl Iterator<Item = BlockRef>) -> (Vec<u64>, Vec<u8>) {
    let mut numbers = Vec::new();
    let mut hashes = Vec::new();
    for block in blocks {
        numbers.push(block.number);
        hashes.extend_from_slice(&block.hash);
    }
    (numbers, hashes)
}

/// Splits a cursor into its envelope flag and fields.
fn cursor_fields(cursor: Option<Position>) -> (u8, u64, u64) {
    match cursor {
        Some(pos) => (1, pos.block, pos.log_index),
        None => (0, 0, 0),
    }
}

/// Builds and frames one envelope from fold state, cursor, and observed blocks.
fn encode_envelope<F: Persist>(
    fold: &F,
    cursor: Option<Position>,
    blocks: impl Iterator<Item = BlockRef>,
    out: &mut Vec<u8>,
) -> Result<(), SnapshotError<F::PersistError>> {
    let (ring_numbers, ring_hashes) = ring_lanes(blocks);
    let (cursor_set, cursor_block, cursor_log_index) = cursor_fields(cursor);
    let mut state = Vec::new();
    fold.encode_state(&mut state);
    let envelope = Envelope {
        magic: SNAPSHOT_MAGIC,
        version: SNAPSHOT_VERSION,
        tag: F::STATE_TAG.as_bytes().to_vec(),
        cursor_set,
        cursor_block,
        cursor_log_index,
        ring_numbers,
        ring_hashes,
        state,
    };
    write_envelope(&envelope, out)
}

/// Errors from encoding or decoding a snapshot envelope.
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
    /// Stored ring's newest block differs from the stored cursor block.
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
                    "snapshot ring's newest block does not match the cursor block"
                )
            }
            Self::Config(error) => write!(f, "snapshot config invalid: {error}"),
            Self::State(error) => write!(f, "snapshot state failed to decode: {error}"),
        }
    }
}

impl<E: fmt::Debug + fmt::Display> core::error::Error for SnapshotError<E> {}

#[cfg_attr(docsrs, doc(cfg(feature = "wincode")))]
impl<F: Persist> Engine<F> {
    /// Appends the framed envelope: wincode payload plus a CRC32C trailer.
    ///
    /// Fails with `TooLarge` when a field exceeds the engine-owned length ceiling,
    /// leaving `out` as it found it.
    pub fn encode_snapshot(
        &self,
        out: &mut Vec<u8>,
    ) -> Result<(), SnapshotError<F::PersistError>> {
        encode_envelope(self.fold(), self.cursor(), self.observed(), out)
    }

    /// Encodes the oldest retained checkpoint; Ok(None) means nothing is retained and
    /// nothing was appended.
    ///
    /// The returned point is the encoded snapshot's cursor, trailing the live cursor by
    /// the ring's checkpoint coverage.
    pub fn encode_durable_snapshot(
        &self,
        out: &mut Vec<u8>,
    ) -> Result<Option<Position>, SnapshotError<F::PersistError>> {
        let Some(slot) = self.oldest_checkpoint() else {
            return Ok(None);
        };
        let Some(point) = slot.cursor else {
            return Ok(None);
        };
        encode_envelope(&slot.fold, slot.cursor, slot.ring.iter(), out)?;
        Ok(Some(point))
    }

    /// Rebuilds an engine from an envelope; checkpoints, skips, freshness start empty.
    pub fn decode_snapshot(
        bytes: &[u8],
        config: EngineConfig,
    ) -> Result<Self, SnapshotError<F::PersistError>> {
        config.validate().map_err(SnapshotError::Config)?;
        if bytes.len() < MIN_ENVELOPE_LEN {
            return Err(SnapshotError::TooShort);
        }
        if bytes[..MAGIC_LEN] != SNAPSHOT_MAGIC {
            return Err(SnapshotError::BadMagic);
        }
        let version = u16::from_le_bytes([bytes[MAGIC_LEN], bytes[MAGIC_LEN + 1]]);
        if version != SNAPSHOT_VERSION {
            return Err(SnapshotError::BadVersion { got: version });
        }

        let Some((payload, trailer)) = bytes.split_last_chunk::<CRC_LEN>() else {
            return Err(SnapshotError::TooShort);
        };
        let expected_crc = u32::from_le_bytes(*trailer);
        let computed_crc = crc32c(payload);
        if computed_crc != expected_crc {
            return Err(SnapshotError::Crc {
                expected: expected_crc,
                got: computed_crc,
            });
        }

        let envelope: Envelope = wincode::config::deserialize(payload, ENVELOPE_CONFIG)
            .map_err(|_| SnapshotError::Envelope)?;
        if envelope.tag.as_slice() != F::STATE_TAG.as_bytes() {
            return Err(SnapshotError::BadTag);
        }

        if envelope.ring_numbers.len() > config.ring_capacity {
            return Err(SnapshotError::RingExceedsCapacity {
                len: envelope.ring_numbers.len(),
                capacity: config.ring_capacity,
            });
        }
        if envelope
            .ring_numbers
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
        {
            return Err(SnapshotError::RingNotAscending);
        }
        // The capacity check above bounds the count, so the product cannot overflow;
        // saturation would still fail the comparison.
        if envelope.ring_hashes.len()
            != envelope.ring_numbers.len().saturating_mul(HASH_LEN)
        {
            return Err(SnapshotError::RingHashLenMismatch);
        }
        let cursor = (envelope.cursor_set != 0)
            .then(|| Position::new(envelope.cursor_block, envelope.cursor_log_index));
        if let Some(pos) = cursor
            && envelope.ring_numbers.last() != Some(&pos.block)
        {
            return Err(SnapshotError::RingCursorMismatch);
        }

        let fold = F::decode_state(&envelope.state).map_err(SnapshotError::State)?;

        let mut ring = BlockRing::with_capacity(config.ring_capacity);
        let lanes = envelope
            .ring_numbers
            .iter()
            .zip(envelope.ring_hashes.chunks_exact(HASH_LEN));
        for (&number, hash) in lanes {
            ring.push(BlockRef {
                number,
                hash: hash
                    .try_into()
                    .map_err(|_| SnapshotError::RingHashLenMismatch)?,
            });
        }

        let mut engine = Engine::new(fold, config).map_err(SnapshotError::Config)?;
        engine.restore_cursor_and_ring(cursor, ring);
        Ok(engine)
    }
}

/// Hand-builds and frames an envelope with caller-chosen fields, for adversarial tests.
#[cfg(test)]
fn encode_custom(
    tag: &[u8],
    cursor: Option<Position>,
    ring: &[BlockRef],
    state: Vec<u8>,
) -> Vec<u8> {
    let (ring_numbers, ring_hashes) = ring_lanes(ring.iter().copied());
    let (cursor_set, cursor_block, cursor_log_index) = cursor_fields(cursor);
    let envelope = Envelope {
        magic: SNAPSHOT_MAGIC,
        version: SNAPSHOT_VERSION,
        tag: tag.to_vec(),
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
        batch::{
            Batch,
            BlockSpan,
            LogEvent,
        },
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
        spans: Vec<(BlockRef, Vec<u64>)>,
    ) -> Batch<u64> {
        let mut events = Vec::new();
        let mut built_spans = Vec::new();
        for (block, log_indices) in spans {
            let start = events.len() as u32;
            for log_index in log_indices {
                events.push(LogEvent {
                    log_index,
                    event: log_index,
                });
            }
            let end = events.len() as u32;
            built_spans.push(BlockSpan { block, start, end });
        }
        Batch {
            boundary,
            spans: built_spans,
            events,
        }
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
        let checkpoint_view = engine.view();
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
        assert_eq!(decoded.view(), checkpoint_view);
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
        assert_eq!(decoded.view(), engine.view());
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
        assert_eq!(decoded.view(), engine.view());
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
}
