//! Fixed 64-byte manifest slot: version, cursor, snapshot id, CRC32C trailer.

use crate::{
    position::Position,
    snapshot::crc32c,
};

/// Byte width of a little-endian u64 field.
const U64_LEN: usize = 8;
/// Byte width of the cursor-present flag.
const FLAG_LEN: usize = 1;
/// Byte width of the CRC32C trailer.
const CRC_LEN: usize = 4;

const VERSION_OFFSET: usize = 0;
const CURSOR_FLAG_OFFSET: usize = VERSION_OFFSET + U64_LEN;
const CURSOR_BLOCK_OFFSET: usize = CURSOR_FLAG_OFFSET + FLAG_LEN;
const CURSOR_LOG_INDEX_OFFSET: usize = CURSOR_BLOCK_OFFSET + U64_LEN;
const SNAPSHOT_ID_OFFSET: usize = CURSOR_LOG_INDEX_OFFSET + U64_LEN;
/// Byte length of the CRC-covered region: every field up to the zero padding.
const CRC_COVERED_LEN: usize = 60;
const CRC_OFFSET: usize = CRC_COVERED_LEN;

/// Byte length of one encoded manifest slot.
pub(crate) const SLOT_SIZE: usize = CRC_OFFSET + CRC_LEN;

/// Byte offset between the two slots: one page, so they never share a failure domain
pub(crate) const SLOT_STRIDE: usize = 4096;

/// Byte length of the whole manifest: the second slot one stride in.
pub(crate) const MANIFEST_SIZE: usize = SLOT_STRIDE + SLOT_SIZE;
/// Manifest file name within a store directory; read by the snapshot store.
pub(crate) const MANIFEST_FILE: &str = "manifest";

/// One manifest slot: durability version, cursor position, and active snapshot id.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct SlotRecord {
    pub(crate) version: u64,
    pub(crate) cursor: Option<Position>,
    pub(crate) snapshot_id: u64,
}

/// Splits a cursor into its slot flag and fields.
fn cursor_flag_and_fields(cursor: Option<Position>) -> (u8, u64, u64) {
    match cursor {
        Some(pos) => (1, pos.block, pos.log_index),
        None => (0, 0, 0),
    }
}

/// Encodes a slot into its fixed layout with a CRC32C trailer over bytes `0..60`.
pub(crate) fn encode_slot(record: &SlotRecord) -> [u8; SLOT_SIZE] {
    let mut bytes = [0u8; SLOT_SIZE];
    bytes[VERSION_OFFSET..VERSION_OFFSET + U64_LEN]
        .copy_from_slice(&record.version.to_le_bytes());
    let (flag, block, log_index) = cursor_flag_and_fields(record.cursor);
    bytes[CURSOR_FLAG_OFFSET] = flag;
    bytes[CURSOR_BLOCK_OFFSET..CURSOR_BLOCK_OFFSET + U64_LEN]
        .copy_from_slice(&block.to_le_bytes());
    bytes[CURSOR_LOG_INDEX_OFFSET..CURSOR_LOG_INDEX_OFFSET + U64_LEN]
        .copy_from_slice(&log_index.to_le_bytes());
    bytes[SNAPSHOT_ID_OFFSET..SNAPSHOT_ID_OFFSET + U64_LEN]
        .copy_from_slice(&record.snapshot_id.to_le_bytes());
    let crc = crc32c(&bytes[..CRC_COVERED_LEN]);
    bytes[CRC_OFFSET..CRC_OFFSET + CRC_LEN].copy_from_slice(&crc.to_le_bytes());
    bytes
}

/// Decodes a slot, returning None on bad length, bad CRC, or an invalid cursor flag.
pub(crate) fn decode_slot(bytes: &[u8]) -> Option<SlotRecord> {
    if bytes.len() != SLOT_SIZE {
        return None;
    }
    let expected_crc = u32::from_le_bytes(
        bytes[CRC_OFFSET..CRC_OFFSET + CRC_LEN]
            .try_into()
            .expect("slice length matches the CRC field width"),
    );
    let computed_crc = crc32c(&bytes[..CRC_COVERED_LEN]);
    if computed_crc != expected_crc {
        return None;
    }
    let version = u64::from_le_bytes(
        bytes[VERSION_OFFSET..VERSION_OFFSET + U64_LEN]
            .try_into()
            .expect("slice length matches a u64 field width"),
    );
    let block = u64::from_le_bytes(
        bytes[CURSOR_BLOCK_OFFSET..CURSOR_BLOCK_OFFSET + U64_LEN]
            .try_into()
            .expect("slice length matches a u64 field width"),
    );
    let log_index = u64::from_le_bytes(
        bytes[CURSOR_LOG_INDEX_OFFSET..CURSOR_LOG_INDEX_OFFSET + U64_LEN]
            .try_into()
            .expect("slice length matches a u64 field width"),
    );
    let cursor = match bytes[CURSOR_FLAG_OFFSET] {
        0 => None,
        1 => Some(Position::new(block, log_index)),
        _ => return None,
    };
    let snapshot_id = u64::from_le_bytes(
        bytes[SNAPSHOT_ID_OFFSET..SNAPSHOT_ID_OFFSET + U64_LEN]
            .try_into()
            .expect("slice length matches a u64 field width"),
    );
    Some(SlotRecord {
        version,
        cursor,
        snapshot_id,
    })
}

#[cfg(test)]
mod tests {
    use super::{
        SLOT_SIZE,
        SlotRecord,
        decode_slot,
        encode_slot,
    };
    use crate::position::Position;

    #[test]
    fn slot_round_trips_through_encode_decode() {
        // given a record with a cursor and a record without one
        let with_cursor = SlotRecord {
            version: 7,
            cursor: Some(Position::new(100, 3)),
            snapshot_id: 12,
        };
        let without_cursor = SlotRecord {
            version: 1,
            cursor: None,
            snapshot_id: 0,
        };
        // when encoded and decoded
        let decoded_with = decode_slot(&encode_slot(&with_cursor));
        let decoded_without = decode_slot(&encode_slot(&without_cursor));
        // then both round trip equal
        assert_eq!(decoded_with, Some(with_cursor));
        assert_eq!(decoded_without, Some(without_cursor));
    }

    #[test]
    fn slot_rejects_torn_bytes() {
        // given an encoded slot
        let record = SlotRecord {
            version: 3,
            cursor: Some(Position::new(9, 1)),
            snapshot_id: 5,
        };
        let bytes = encode_slot(&record);
        // when any single byte is flipped
        for index in 0..SLOT_SIZE {
            let mut torn = bytes;
            torn[index] = !torn[index];
            // then decode returns None
            assert_eq!(
                decode_slot(&torn),
                None,
                "byte {index} should invalidate the slot"
            );
        }
    }

    #[test]
    fn slot_rejects_wrong_length() {
        // given 63 bytes
        let short = [0u8; SLOT_SIZE - 1];
        // when decoded
        let result = decode_slot(&short);
        // then None
        assert_eq!(result, None);
    }
}
