//! Durable snapshot home: temp-fsync-rename commits, dual-slot manifest.

use std::{
    io,
    path::{
        Path,
        PathBuf,
    },
};

use core::fmt;

use crate::{
    position::Position,
    storage::{
        manifest::{
            MANIFEST_FILE,
            MANIFEST_SIZE,
            SLOT_SIZE,
            SLOT_STRIDE,
            SlotRecord,
            decode_slot,
            encode_slot,
        },
        vfs::Vfs,
    },
};

/// Temp file name a commit writes before renaming it into place.
const TEMP_FILE: &str = "snap.tmp";
/// Prefix of a durable snapshot file's name.
const SNAPSHOT_PREFIX: &str = "snap-";
/// Suffix of a durable snapshot file's name.
const SNAPSHOT_SUFFIX: &str = ".bin";

/// Builds the file name for a snapshot with the given id.
fn snapshot_file_name(id: u64) -> String {
    format!("{SNAPSHOT_PREFIX}{id}{SNAPSHOT_SUFFIX}")
}

/// Recovers a snapshot id from a file name, or None if it doesn't match the pattern.
fn snapshot_id_from_path(path: &Path) -> Option<u64> {
    let name = path.file_name()?.to_str()?;
    let id: u64 = name
        .strip_prefix(SNAPSHOT_PREFIX)?
        .strip_suffix(SNAPSHOT_SUFFIX)?
        .parse()
        .ok()?;
    (snapshot_file_name(id) == name).then_some(id)
}

/// True when the manifest carries no slot any commit ever wrote: short or all zero.
///
/// An acknowledged commit always leaves one full, checksum-valid slot behind, and slots
/// are only ever overwritten in place, so this shape means the store is still fresh.
fn manifest_is_uninitialized(bytes: &[u8]) -> bool {
    bytes.len() < SLOT_SIZE * 2 || bytes.iter().all(|byte| *byte == 0)
}

/// Maps a missing path to None so callers act once instead of checking then acting.
///
/// Every caller races an unlink: a prior crash repair, a concurrent prune, or an
/// operator clearing the directory. Checking first only widens the window.
fn missing_ok<T>(result: io::Result<T>) -> io::Result<Option<T>> {
    match result {
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
        other => other.map(Some),
    }
}

/// Directory home for a snapshot store and how many superseded snapshots to keep.
#[derive(Debug, Clone)]
pub struct StoreConfig {
    /// Directory the manifest and snapshot files live in.
    pub dir: PathBuf,
    /// Snapshot files kept beyond the two the manifest references; minimum 1.
    pub retain: usize,
}

/// Snapshot bytes and cursor recovered from a durable store on open.
#[derive(Debug)]
pub struct Recovered {
    /// Snapshot bytes the manifest points at.
    pub snapshot: Vec<u8>,
    /// Cursor the committing engine had reached.
    pub cursor: Option<Position>,
}

/// Failure opening or committing to a snapshot store.
#[derive(Debug)]
pub enum StoreError {
    /// Filesystem operation failed.
    Io(io::Error),
    /// Manifest holds written bytes but neither slot passes its checksum.
    CorruptManifest,
    /// Manifest points at a snapshot file that is absent.
    MissingSnapshot {
        /// Snapshot id the manifest names.
        id: u64,
    },
    /// Configured retain count keeps no snapshot.
    RetainZero,
    /// A prior commit failed, so this store refuses further commits.
    Poisoned,
}

impl fmt::Display for StoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(error) => write!(f, "snapshot store io error: {error}"),
            Self::CorruptManifest => {
                write!(f, "manifest exists but neither slot passes its checksum")
            }
            Self::MissingSnapshot { id } => {
                write!(f, "manifest points at missing snapshot {id}")
            }
            Self::RetainZero => write!(f, "retain must keep at least one snapshot"),
            Self::Poisoned => {
                write!(f, "store refuses commits after an earlier commit failed")
            }
        }
    }
}

impl core::error::Error for StoreError {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            Self::CorruptManifest
            | Self::MissingSnapshot { .. }
            | Self::RetainZero
            | Self::Poisoned => None,
        }
    }
}

impl From<io::Error> for StoreError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

/// Durable snapshot home: temp-fsync-rename commits, dual-slot manifest.
pub struct SnapshotStore<V: Vfs> {
    dir: PathBuf,
    vfs: V,
    retain: usize,
    slots: [Option<SlotRecord>; 2],
    active: usize,
    poisoned: bool,
}

impl<V: Vfs> SnapshotStore<V> {
    /// Opens or initializes the directory; returns the recovered state if any.
    pub fn open(
        config: StoreConfig,
        mut vfs: V,
    ) -> Result<(Self, Option<Recovered>), StoreError> {
        if config.retain == 0 {
            return Err(StoreError::RetainZero);
        }
        vfs.create_dir_all(&config.dir)?;

        let temp_path = config.dir.join(TEMP_FILE);
        if missing_ok(vfs.remove(&temp_path))?.is_some() {
            // Syncs the repair so the removal survives a later crash.
            vfs.fsync_dir(&config.dir)?;
        }

        let manifest_path = config.dir.join(MANIFEST_FILE);
        let slots = match missing_ok(vfs.read(&manifest_path))? {
            Some(bytes) => {
                let left = bytes.get(0..SLOT_SIZE).and_then(decode_slot);
                let right = bytes
                    .get(SLOT_STRIDE..SLOT_STRIDE + SLOT_SIZE)
                    .and_then(decode_slot);
                if left.is_none() && right.is_none() && !manifest_is_uninitialized(&bytes)
                {
                    return Err(StoreError::CorruptManifest);
                }
                [left, right]
            }
            // Creates the manifest with blank slots so it exists before any commit;
            // the first commit's own directory fsync durably registers its name.
            None => {
                vfs.write(&manifest_path, &[0u8; MANIFEST_SIZE])?;
                [None, None]
            }
        };

        let active = match (slots[0], slots[1]) {
            (Some(left), Some(right)) if right.version > left.version => 1,
            (None, Some(_)) => 1,
            _ => 0,
        };

        let recovered = match slots[active] {
            None => None,
            Some(record) => {
                let snapshot_path =
                    config.dir.join(snapshot_file_name(record.snapshot_id));
                let snapshot = missing_ok(vfs.read(&snapshot_path))?.ok_or(
                    StoreError::MissingSnapshot {
                        id: record.snapshot_id,
                    },
                )?;
                Some(Recovered {
                    snapshot,
                    cursor: record.cursor,
                })
            }
        };

        let mut store = Self {
            dir: config.dir,
            vfs,
            retain: config.retain,
            slots,
            active,
            poisoned: false,
        };
        // Reclaiming space is best effort; the next open retries whatever it leaves.
        let _ = store.prune();
        Ok((store, recovered))
    }

    /// Durably commits one snapshot and moves the cursor watermark onto it.
    ///
    /// | crash lands | on-disk state | recovery |
    /// |---|---|---|
    /// | during or after the temp write, before its fsync | orphan temp file | temp removed, prior snapshot serves |
    /// | after the temp fsync, before the rename | orphan temp file | temp removed, prior snapshot serves |
    /// | after the rename, before the directory fsync | rename possibly volatile | manifest still points at the prior snapshot either way |
    /// | during the manifest slot write | torn newer slot, bad CRC | other slot valid, prior snapshot serves |
    /// | after the slot write, before its fsync | new slot volatile, maybe torn | whichever valid slot has the higher version serves; both outcomes are acknowledged states |
    /// | after the manifest fsync | both slots valid | new snapshot serves |
    /// | during pruning | unreferenced files linger | pruned on next open |
    pub fn commit(
        &mut self,
        snapshot: &[u8],
        cursor: Option<Position>,
    ) -> Result<(), StoreError> {
        if self.poisoned {
            return Err(StoreError::Poisoned);
        }
        let result = self.commit_once(snapshot, cursor);
        if result.is_err() {
            self.poisoned = true;
        }
        result
    }

    fn commit_once(
        &mut self,
        snapshot: &[u8],
        cursor: Option<Position>,
    ) -> Result<(), StoreError> {
        let current_version = self.slots[self.active].map_or(0, |slot| slot.version);
        let next_version = current_version
            .checked_add(1)
            .expect("snapshot version counter overflow");
        let older = 1 - self.active;

        let temp_path = self.dir.join(TEMP_FILE);
        let snapshot_path = self.dir.join(snapshot_file_name(next_version));
        self.vfs.write(&temp_path, snapshot)?;
        self.vfs.fsync_file(&temp_path)?;
        self.vfs.rename(&temp_path, &snapshot_path)?;
        self.vfs.fsync_dir(&self.dir)?;

        let record = SlotRecord {
            version: next_version,
            cursor,
            snapshot_id: next_version,
        };
        let slot_bytes = encode_slot(&record);
        let slot_offset =
            u64::try_from(older * SLOT_STRIDE).expect("slot offset fits in a u64");
        let manifest_path = self.dir.join(MANIFEST_FILE);
        self.vfs
            .write_at(&manifest_path, slot_offset, &slot_bytes)?;
        self.vfs.fsync_file(&manifest_path)?;

        // Commit point: the manifest fsync returned Ok, so flip the active slot now.
        self.slots[older] = Some(record);
        self.active = older;

        // Reclaiming space runs past the commit point; the next open retries it.
        let _ = self.prune();
        Ok(())
    }

    /// Cursor of the snapshot the manifest points at; what a reopen recovers.
    pub fn durable_cursor(&self) -> Option<Position> {
        self.slots[self.active].and_then(|slot| slot.cursor)
    }

    /// Returns the underlying filesystem, consuming the store.
    pub fn into_vfs(self) -> V {
        self.vfs
    }

    /// Removes snapshot files referenced by neither slot, oldest first, keeping
    /// `retain` extras; the pointer removal became durable in the manifest fsync
    /// above, so unlinking an unreferenced file here never loses acknowledged data.
    fn prune(&mut self) -> Result<(), StoreError> {
        let referenced = self.slots.map(|slot| slot.map(|slot| slot.snapshot_id));
        let mut unreferenced: Vec<u64> = self
            .vfs
            .list(&self.dir)?
            .iter()
            .filter_map(|path| snapshot_id_from_path(path))
            .filter(|id| !referenced.contains(&Some(*id)))
            .collect();
        unreferenced.sort_unstable();
        let remove_count = unreferenced.len().saturating_sub(self.retain);
        for id in &unreferenced[..remove_count] {
            missing_ok(self.vfs.remove(&self.dir.join(snapshot_file_name(*id))))?;
        }
        if remove_count > 0 {
            // Syncs the unlinks so repeated crash-open cycles converge.
            self.vfs.fsync_dir(&self.dir)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        storage::vfs::RealVfs,
        test_util::CrashVfs,
    };

    fn config(dir: PathBuf, retain: usize) -> StoreConfig {
        StoreConfig { dir, retain }
    }

    #[test]
    fn fresh_dir_opens_empty() {
        // given an empty CrashVfs
        let vfs = CrashVfs::new();
        // when opened
        let (_, recovered) =
            SnapshotStore::open(config(PathBuf::from("/store"), 1), vfs).unwrap();
        // then no recovery
        assert!(recovered.is_none());
    }

    #[test]
    fn commit_then_open_recovers_bytes_and_cursor() {
        // given one commit
        let dir = PathBuf::from("/store");
        let (mut store, _) =
            SnapshotStore::open(config(dir.clone(), 1), CrashVfs::new()).unwrap();
        let cursor = Some(Position::new(10, 2));
        store.commit(b"snapshot-bytes", cursor).unwrap();
        let vfs = store.into_vfs();
        // when reopened
        let (_, recovered) = SnapshotStore::open(config(dir, 1), vfs).unwrap();
        // then the exact bytes and cursor return
        let recovered = recovered.unwrap();
        assert_eq!(recovered.snapshot.as_slice(), b"snapshot-bytes".as_slice());
        assert_eq!(recovered.cursor, cursor);
    }

    #[test]
    fn second_commit_supersedes_first() {
        // given two commits
        let dir = PathBuf::from("/store");
        let (mut store, _) =
            SnapshotStore::open(config(dir.clone(), 1), CrashVfs::new()).unwrap();
        store.commit(b"first", Some(Position::new(1, 0))).unwrap();
        store.commit(b"second", Some(Position::new(2, 0))).unwrap();
        let durable = store.durable_cursor();
        let vfs = store.into_vfs();
        // when reopened
        let (_, recovered) = SnapshotStore::open(config(dir, 1), vfs).unwrap();
        // then the second serves and durable_cursor matches
        let recovered = recovered.unwrap();
        assert_eq!(recovered.snapshot.as_slice(), b"second".as_slice());
        assert_eq!(durable, Some(Position::new(2, 0)));
    }

    #[test]
    fn crash_at_every_op_of_a_commit_recovers_a_valid_state() {
        // given a store with one durable commit
        let dir = PathBuf::from("/store");
        let torn_len = 8;

        let (mut measure_first, _) =
            SnapshotStore::open(config(dir.clone(), 1), CrashVfs::new()).unwrap();
        measure_first
            .commit(b"first", Some(Position::new(1, 0)))
            .unwrap();
        let after_first = measure_first.into_vfs().op_count();

        let (mut measure_second, _) =
            SnapshotStore::open(config(dir.clone(), 1), CrashVfs::new()).unwrap();
        measure_second
            .commit(b"first", Some(Position::new(1, 0)))
            .unwrap();
        measure_second
            .commit(b"second", Some(Position::new(2, 0)))
            .unwrap();
        let after_second = measure_second.into_vfs().op_count();
        let second_commit_ops = after_second - after_first;

        // when the commit crashes at every op budget from 0 to the total op count
        for budget in 0..=second_commit_ops {
            let vfs = CrashVfs::with_crash_budget(after_first + budget, torn_len);
            let (mut store, _) =
                SnapshotStore::open(config(dir.clone(), 1), vfs).unwrap();
            store.commit(b"first", Some(Position::new(1, 0))).unwrap();
            let commit_result = store.commit(b"second", Some(Position::new(2, 0)));
            let mut vfs = store.into_vfs();
            vfs.crash();
            let (_, recovered) =
                SnapshotStore::open(config(dir.clone(), 1), vfs).unwrap();
            // then open succeeds and recovers exactly one acknowledged snapshot
            let recovered = recovered
                .unwrap_or_else(|| panic!("budget {budget} lost every snapshot"));
            if commit_result.is_err() {
                assert_eq!(
                    recovered.snapshot.as_slice(),
                    b"first".as_slice(),
                    "budget {budget} should still recover the first snapshot"
                );
            } else {
                assert_eq!(
                    recovered.snapshot.as_slice(),
                    b"second".as_slice(),
                    "budget {budget} completed the commit and should recover the second"
                );
            }
        }
    }

    #[test]
    fn torn_manifest_slot_falls_back_to_valid_slot() {
        // given a crash mid slot write with a nonzero torn_len
        let dir = PathBuf::from("/store");
        let (mut baseline, _) =
            SnapshotStore::open(config(dir.clone(), 1), CrashVfs::new()).unwrap();
        baseline
            .commit(b"first", Some(Position::new(1, 0)))
            .unwrap();
        let after_first = baseline.into_vfs().op_count();

        let vfs = CrashVfs::with_crash_budget(after_first + 4, 8);
        let (mut store, _) = SnapshotStore::open(config(dir.clone(), 1), vfs).unwrap();
        store.commit(b"first", Some(Position::new(1, 0))).unwrap();
        let result = store.commit(b"second", Some(Position::new(2, 0)));
        let mut vfs = store.into_vfs();
        vfs.crash();
        // when reopened
        let (_, recovered) = SnapshotStore::open(config(dir, 1), vfs).unwrap();
        // then the prior state serves
        assert!(result.is_err());
        assert_eq!(recovered.unwrap().snapshot.as_slice(), b"first".as_slice());
    }

    #[test]
    fn fresh_store_reopens_without_commit() {
        // given a store opened once and dropped before any commit
        let dir = PathBuf::from("/store");
        let (store, _) =
            SnapshotStore::open(config(dir.clone(), 1), CrashVfs::new()).unwrap();
        let vfs = store.into_vfs();
        // when reopened
        let (_, recovered) = SnapshotStore::open(config(dir, 1), vfs).unwrap();
        // then the open succeeds and reports no recovery
        assert!(recovered.is_none());
    }

    #[test]
    fn real_fs_fresh_store_reopens_without_commit() {
        // given a tempdir store opened once through RealVfs and dropped
        let dir = tempfile::tempdir().unwrap();
        let cfg = config(dir.path().to_path_buf(), 1);
        let (store, _) = SnapshotStore::open(cfg.clone(), RealVfs).unwrap();
        let vfs = store.into_vfs();
        // when reopened
        let (_, recovered) = SnapshotStore::open(cfg, vfs).unwrap();
        // then the open succeeds and reports no recovery
        assert!(recovered.is_none());
    }

    #[test]
    fn crash_inside_pruning_still_opens() {
        // given four commits under retain 4 and a budget that expires at the first unlink
        let dir = PathBuf::from("/store");
        let setup_ops = {
            let (mut store, _) =
                SnapshotStore::open(config(dir.clone(), 4), CrashVfs::new()).unwrap();
            for version in 1..=4u64 {
                store
                    .commit(b"snapshot", Some(Position::new(version, 0)))
                    .unwrap();
            }
            store.into_vfs().op_count()
        };
        let vfs = CrashVfs::with_crash_budget(setup_ops, 0);
        let (mut store, _) = SnapshotStore::open(config(dir.clone(), 4), vfs).unwrap();
        for version in 1..=4u64 {
            store
                .commit(b"snapshot", Some(Position::new(version, 0)))
                .unwrap();
        }
        let vfs = store.into_vfs();
        // when reopened with retain 1, so pruning unlinks a superseded snapshot
        let (store, recovered) = SnapshotStore::open(config(dir, 1), vfs).unwrap();
        // then the open succeeds and the acknowledged snapshot still recovers
        assert_eq!(recovered.unwrap().cursor, Some(Position::new(4, 0)));
        assert_eq!(store.durable_cursor(), Some(Position::new(4, 0)));
    }

    #[test]
    fn corrupt_both_slots_is_typed() {
        // given a manifest whose written bytes fail both slot checksums
        let dir = PathBuf::from("/store");
        let mut vfs = CrashVfs::new();
        vfs.create_dir_all(&dir).unwrap();
        let manifest_path = dir.join(MANIFEST_FILE);
        let zeroed = vec![0xABu8; SLOT_SIZE * 2];
        vfs.write(&manifest_path, &zeroed).unwrap();
        vfs.fsync_file(&manifest_path).unwrap();
        vfs.fsync_dir(&dir).unwrap();
        // when opened
        let result = SnapshotStore::open(config(dir, 1), vfs);
        // then CorruptManifest
        assert!(matches!(result, Err(StoreError::CorruptManifest)));
    }

    #[test]
    fn dangling_manifest_pointer_is_typed() {
        // given a valid manifest and a deleted snapshot file
        let dir = PathBuf::from("/store");
        let (mut store, _) =
            SnapshotStore::open(config(dir.clone(), 1), CrashVfs::new()).unwrap();
        store.commit(b"first", Some(Position::new(1, 0))).unwrap();
        let mut vfs = store.into_vfs();
        vfs.remove(&dir.join(snapshot_file_name(1))).unwrap();
        // when opened
        let result = SnapshotStore::open(config(dir, 1), vfs);
        // then MissingSnapshot
        assert!(matches!(result, Err(StoreError::MissingSnapshot { id: 1 })));
    }

    #[test]
    fn orphan_temp_and_unreferenced_snapshots_are_pruned() {
        // given leftover snap.tmp and three old snapshot files with retain 1
        let dir = PathBuf::from("/store");
        let mut vfs = CrashVfs::new();
        vfs.create_dir_all(&dir).unwrap();
        for id in 1..=4u64 {
            let path = dir.join(snapshot_file_name(id));
            vfs.write(&path, format!("snap-{id}").as_bytes()).unwrap();
            vfs.fsync_file(&path).unwrap();
        }
        let temp_path = dir.join(TEMP_FILE);
        vfs.write(&temp_path, b"leftover").unwrap();
        vfs.fsync_file(&temp_path).unwrap();
        vfs.fsync_dir(&dir).unwrap();
        let record = SlotRecord {
            version: 1,
            cursor: None,
            snapshot_id: 4,
        };
        let manifest_path = dir.join(MANIFEST_FILE);
        let mut manifest_bytes = vec![0u8; SLOT_SIZE * 2];
        manifest_bytes[..SLOT_SIZE].copy_from_slice(&encode_slot(&record));
        vfs.write(&manifest_path, &manifest_bytes).unwrap();
        vfs.fsync_file(&manifest_path).unwrap();
        vfs.fsync_dir(&dir).unwrap();
        // when opened with retain 1
        let (store, recovered) =
            SnapshotStore::open(config(dir.clone(), 1), vfs).unwrap();
        assert_eq!(recovered.unwrap().snapshot.as_slice(), b"snap-4".as_slice());
        let mut vfs = store.into_vfs();
        // then temp is gone and only the referenced plus one retained file remain
        let remaining = vfs.list(&dir).unwrap();
        assert!(!remaining.contains(&temp_path));
        assert!(remaining.contains(&dir.join(snapshot_file_name(4))));
        assert!(remaining.contains(&dir.join(snapshot_file_name(3))));
        assert!(!remaining.contains(&dir.join(snapshot_file_name(2))));
        assert!(!remaining.contains(&dir.join(snapshot_file_name(1))));
    }

    #[test]
    fn real_fs_commit_reopen_smoke() {
        // given a tempdir with RealVfs
        let dir = tempfile::tempdir().unwrap();
        let cfg = config(dir.path().to_path_buf(), 1);
        let (mut store, _) = SnapshotStore::open(cfg.clone(), RealVfs).unwrap();
        store
            .commit(b"real-bytes", Some(Position::new(3, 1)))
            .unwrap();
        let vfs = store.into_vfs();
        // when committing and reopening
        let (_, recovered) = SnapshotStore::open(cfg, vfs).unwrap();
        // then recovery matches
        let recovered = recovered.unwrap();
        assert_eq!(recovered.snapshot.as_slice(), b"real-bytes".as_slice());
        assert_eq!(recovered.cursor, Some(Position::new(3, 1)));
    }
}
