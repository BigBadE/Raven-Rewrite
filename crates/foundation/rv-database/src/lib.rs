//! Salsa database setup for incremental compilation
//!
//! This crate provides the core database infrastructure for the Raven compiler.
//! It uses Salsa for incremental computation and memoization.

use anyhow::Result;
use rv_intern::Interner;
use rv_vfs::VirtualFileSystem;
use std::path::PathBuf;
use std::sync::Arc;

/// Input: Source file registered in the system
#[salsa::input]
pub struct SourceFile {
    /// The path to the file
    pub path: PathBuf,
}

/// Main database trait for the Raven compiler
pub trait RavenDb: salsa::Database {
    /// Get the virtual file system
    fn vfs(&self) -> &VirtualFileSystem;

    /// Get the string interner
    fn interner(&self) -> &Interner;
}

/// Root database implementation
#[salsa::db]
#[derive(Clone)]
pub struct RootDatabase {
    storage: salsa::Storage<Self>,
    vfs: VirtualFileSystem,
    interner: Interner,
}

impl RootDatabase {
    /// Creates a new root database
    #[must_use]
    pub fn new() -> Self {
        Self {
            storage: salsa::Storage::default(),
            vfs: VirtualFileSystem::new(),
            interner: Interner::new(),
        }
    }

    /// Registers a file and creates a `SourceFile` input
    ///
    /// # Errors
    ///
    /// Returns an error if file registration fails
    pub fn register_file(&mut self, path: impl Into<PathBuf>) -> Result<SourceFile> {
        let path = path.into();
        let _file_id = self.vfs.register_file(&path)?;
        Ok(SourceFile::new(self, path))
    }

    /// Sets file contents directly (useful for testing)
    ///
    /// # Errors
    ///
    /// Returns an error if the file is not registered
    pub fn set_file_contents(&mut self, source_file: SourceFile, contents: String) -> Result<()> {
        let path = source_file.path(self);
        if let Some(file_id) = self.vfs.get_file_id(path)? {
            self.vfs.set_file_contents(file_id, contents)?;
        }
        Ok(())
    }

    /// Gets file contents
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be read
    pub fn get_file_contents(&self, source_file: SourceFile) -> Result<Arc<String>> {
        let path = source_file.path(self);

        // Try to get file ID from path
        if let Ok(Some(file_id)) = self.vfs.get_file_id(&path) {
            // Try to get cached contents
            if let Ok(Some(contents)) = self.vfs.get_file_contents(file_id) {
                return Ok(Arc::new(contents));
            }
        }

        // Fall back to reading from disk
        Ok(Arc::new(std::fs::read_to_string(&path)?))
    }
}

impl Default for RootDatabase {
    fn default() -> Self {
        Self::new()
    }
}

impl salsa::Database for RootDatabase {}

impl RavenDb for RootDatabase {
    fn vfs(&self) -> &VirtualFileSystem {
        &self.vfs
    }

    fn interner(&self) -> &Interner {
        &self.interner
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_incremental_file_contents() {
        let mut database = RootDatabase::new();
        let source_file = database.register_file("test.rs").unwrap();

        // Set initial contents
        database
            .set_file_contents(source_file, "fn main() {}".to_string())
            .unwrap();
        let contents1 = database.get_file_contents(source_file).unwrap();
        assert_eq!(contents1.as_ref(), "fn main() {}");

        // Update contents - this should invalidate the query
        database
            .set_file_contents(source_file, "fn test() {}".to_string())
            .unwrap();
        let contents2 = database.get_file_contents(source_file).unwrap();
        assert_eq!(contents2.as_ref(), "fn test() {}");
    }
}
