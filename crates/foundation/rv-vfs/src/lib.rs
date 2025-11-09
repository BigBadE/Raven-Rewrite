//! Virtual File System for managing source files
//!
//! Provides an abstraction layer over the file system with file watching capabilities.

use anyhow::Result;
use rustc_hash::FxHashMap;
use rv_span::FileId;
use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock};

/// Virtual File System that tracks source files
pub struct VirtualFileSystem {
    inner: Arc<RwLock<VfsInner>>,
}

struct VfsInner {
    files: FxHashMap<FileId, FileData>,
    paths: FxHashMap<PathBuf, FileId>,
    next_id: u32,
}

/// Data associated with a file
#[derive(Clone, Debug)]
pub struct FileData {
    /// Canonical path to the file
    pub path: PathBuf,
    /// File contents (if loaded)
    pub contents: Option<String>,
}

impl VirtualFileSystem {
    /// Creates a new empty virtual file system
    #[must_use]
    pub fn new() -> Self {
        Self {
            inner: Arc::new(RwLock::new(VfsInner {
                files: FxHashMap::default(),
                paths: FxHashMap::default(),
                next_id: 0,
            })),
        }
    }

    /// Registers a file path and returns its ID
    ///
    /// # Errors
    ///
    /// Returns an error if the lock is poisoned
    pub fn register_file(&self, path: impl AsRef<Path>) -> Result<FileId> {
        let path = path.as_ref().to_path_buf();
        let mut inner = self
            .inner
            .write()
            .map_err(|_| anyhow::anyhow!("Lock poisoned"))?;

        // Check if already registered
        if let Some(&file_id) = inner.paths.get(&path) {
            return Ok(file_id);
        }

        // Create new file ID
        let file_id = FileId::new(inner.next_id);
        inner.next_id += 1;

        // Register file
        inner.files.insert(
            file_id,
            FileData {
                path: path.clone(),
                contents: None,
            },
        );
        inner.paths.insert(path, file_id);

        Ok(file_id)
    }

    /// Loads file contents from disk
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be read or the lock is poisoned
    pub fn load_file(&self, file_id: FileId) -> Result<String> {
        let path = {
            let inner = self
                .inner
                .read()
                .map_err(|_| anyhow::anyhow!("Lock poisoned"))?;
            inner
                .files
                .get(&file_id)
                .ok_or_else(|| anyhow::anyhow!("File not found: {:?}", file_id))?
                .path
                .clone()
        };

        let contents = std::fs::read_to_string(&path)?;

        // Cache contents
        let mut inner = self
            .inner
            .write()
            .map_err(|_| anyhow::anyhow!("Lock poisoned"))?;
        if let Some(file_data) = inner.files.get_mut(&file_id) {
            file_data.contents = Some(contents.clone());
        }

        Ok(contents)
    }

    /// Sets file contents (useful for testing or in-memory files)
    ///
    /// # Errors
    ///
    /// Returns an error if the lock is poisoned or file doesn't exist
    pub fn set_file_contents(&self, file_id: FileId, contents: String) -> Result<()> {
        let mut inner = self
            .inner
            .write()
            .map_err(|_| anyhow::anyhow!("Lock poisoned"))?;
        let file_data = inner
            .files
            .get_mut(&file_id)
            .ok_or_else(|| anyhow::anyhow!("File not found: {:?}", file_id))?;
        file_data.contents = Some(contents);
        Ok(())
    }

    /// Gets cached file contents (if available)
    ///
    /// # Errors
    ///
    /// Returns an error if the lock is poisoned or file doesn't exist
    pub fn get_file_contents(&self, file_id: FileId) -> Result<Option<String>> {
        let inner = self
            .inner
            .read()
            .map_err(|_| anyhow::anyhow!("Lock poisoned"))?;
        Ok(inner
            .files
            .get(&file_id)
            .and_then(|data| data.contents.clone()))
    }

    /// Gets file path
    ///
    /// # Errors
    ///
    /// Returns an error if the lock is poisoned or file doesn't exist
    pub fn get_file_path(&self, file_id: FileId) -> Result<PathBuf> {
        let inner = self
            .inner
            .read()
            .map_err(|_| anyhow::anyhow!("Lock poisoned"))?;
        Ok(inner
            .files
            .get(&file_id)
            .ok_or_else(|| anyhow::anyhow!("File not found: {:?}", file_id))?
            .path
            .clone())
    }

    /// Gets file ID from path
    ///
    /// # Errors
    ///
    /// Returns an error if the lock is poisoned
    pub fn get_file_id(&self, path: impl AsRef<Path>) -> Result<Option<FileId>> {
        let inner = self
            .inner
            .read()
            .map_err(|_| anyhow::anyhow!("Lock poisoned"))?;
        Ok(inner.paths.get(path.as_ref()).copied())
    }
}

impl Default for VirtualFileSystem {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for VirtualFileSystem {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_duplicate_registration() {
        let vfs = VirtualFileSystem::new();
        let id1 = vfs.register_file("test.rs").unwrap();
        let id2 = vfs.register_file("test.rs").unwrap();
        assert_eq!(id1, id2);
    }
}
