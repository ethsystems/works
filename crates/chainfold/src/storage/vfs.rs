//! Filesystem abstraction the durability protocol is built from.

use std::{
    fs,
    io,
    io::{
        Seek,
        SeekFrom,
        Write,
    },
    path::{
        Path,
        PathBuf,
    },
};

/// Filesystem primitives the durability protocol is built from.
pub trait Vfs {
    /// Creates the directory and every missing parent.
    fn create_dir_all(&mut self, path: &Path) -> io::Result<()>;
    /// Reads a whole file.
    fn read(&mut self, path: &Path) -> io::Result<Vec<u8>>;
    /// Writes the full file contents, creating or truncating as needed.
    fn write(&mut self, path: &Path, bytes: &[u8]) -> io::Result<()>;
    /// Writes bytes at an offset into an existing or new file, without truncating it.
    fn write_at(&mut self, path: &Path, offset: u64, bytes: &[u8]) -> io::Result<()>;
    /// Makes the file's own contents durable; the containing directory entry is not.
    fn fsync_file(&mut self, path: &Path) -> io::Result<()>;
    /// Moves a file to a new name within the same directory.
    fn rename(&mut self, from: &Path, to: &Path) -> io::Result<()>;
    /// Unlinks a file.
    fn remove(&mut self, path: &Path) -> io::Result<()>;
    /// Lists the paths directly inside a directory.
    fn list(&mut self, dir: &Path) -> io::Result<Vec<PathBuf>>;
    /// Makes name changes within the directory durable.
    fn fsync_dir(&mut self, path: &Path) -> io::Result<()>;
    /// True when the path resolves to an existing file.
    fn exists(&mut self, path: &Path) -> io::Result<bool>;
}

/// Vfs over std::fs.
#[derive(Debug, Default, Clone, Copy)]
pub struct RealVfs;

impl Vfs for RealVfs {
    fn create_dir_all(&mut self, path: &Path) -> io::Result<()> {
        fs::create_dir_all(path)
    }

    fn read(&mut self, path: &Path) -> io::Result<Vec<u8>> {
        fs::read(path)
    }

    fn write(&mut self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        fs::write(path, bytes)
    }

    fn write_at(&mut self, path: &Path, offset: u64, bytes: &[u8]) -> io::Result<()> {
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(false)
            .open(path)?;
        file.seek(SeekFrom::Start(offset))?;
        file.write_all(bytes)
    }

    fn fsync_file(&mut self, path: &Path) -> io::Result<()> {
        fs::File::open(path)?.sync_all()
    }

    fn rename(&mut self, from: &Path, to: &Path) -> io::Result<()> {
        fs::rename(from, to)
    }

    fn remove(&mut self, path: &Path) -> io::Result<()> {
        fs::remove_file(path)
    }

    fn list(&mut self, dir: &Path) -> io::Result<Vec<PathBuf>> {
        fs::read_dir(dir)?
            .map(|entry| entry.map(|e| e.path()))
            .collect()
    }

    fn fsync_dir(&mut self, path: &Path) -> io::Result<()> {
        match fs::File::open(path)?.sync_all() {
            Err(error)
                if matches!(
                    error.kind(),
                    io::ErrorKind::InvalidInput | io::ErrorKind::Unsupported
                ) =>
            {
                Ok(())
            }
            result => result,
        }
    }

    fn exists(&mut self, path: &Path) -> io::Result<bool> {
        path.try_exists()
    }
}

#[cfg(test)]
mod tests {
    use tempfile::tempdir;

    use super::{
        RealVfs,
        Vfs,
    };

    #[test]
    fn real_vfs_round_trips_files() {
        // given a tempdir and a RealVfs
        let dir = tempdir().unwrap();
        let mut vfs = RealVfs;
        let original = dir.path().join("original.bin");
        let renamed = dir.path().join("renamed.bin");
        let bytes = b"chainfold storage".to_vec();
        // when writing, syncing, renaming, listing, and reading through RealVfs
        vfs.write(&original, &bytes).unwrap();
        vfs.fsync_file(&original).unwrap();
        vfs.rename(&original, &renamed).unwrap();
        vfs.fsync_dir(dir.path()).unwrap();
        let listed = vfs.list(dir.path()).unwrap();
        let read_back = vfs.read(&renamed).unwrap();
        // then contents and names match
        assert!(!vfs.exists(&original).unwrap());
        assert!(vfs.exists(&renamed).unwrap());
        assert_eq!(listed, vec![renamed.clone()]);
        assert_eq!(read_back, bytes);
    }
}
