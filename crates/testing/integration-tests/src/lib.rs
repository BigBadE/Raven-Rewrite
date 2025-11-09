//! Integration test utilities for the Raven compiler

use anyhow::Result;
use rv_database::{RootDatabase, SourceFile};
use std::fs;
use std::path::{Path, PathBuf};

/// Test fixture helper
pub struct TestFixture {
    /// Database instance
    pub db: RootDatabase,
    /// Files registered in the fixture
    pub files: Vec<SourceFile>,
}

impl TestFixture {
    /// Creates a new test fixture
    #[must_use]
    pub fn new() -> Self {
        Self {
            db: RootDatabase::new(),
            files: Vec::new(),
        }
    }

    /// Adds a file to the fixture
    ///
    /// # Errors
    ///
    /// Returns an error if file registration fails
    pub fn add_file(&mut self, path: &str, contents: &str) -> Result<SourceFile> {
        // Use absolute path to avoid filesystem lookup issues in tests
        let absolute_path = if Path::new(path).is_absolute() {
            PathBuf::from(path)
        } else {
            std::env::current_dir()
                .unwrap_or_default()
                .join("test_fixtures")
                .join(path)
        };

        let source_file = self.db.register_file(absolute_path)?;
        self.db
            .set_file_contents(source_file, contents.to_string())?;
        self.files.push(source_file);
        Ok(source_file)
    }

    /// Loads an entire directory as a test fixture
    ///
    /// Recursively walks the directory and loads all `.rs` files,
    /// preserving the directory structure in the file paths.
    ///
    /// # Errors
    ///
    /// Returns an error if directory traversal or file reading fails
    pub fn from_dir(dir: impl AsRef<Path>) -> Result<Self> {
        let mut test_fixture = Self::new();
        let base_path = dir.as_ref();

        Self::load_dir_recursive(&mut test_fixture, base_path, base_path)?;

        Ok(test_fixture)
    }

    /// Recursively loads files from a directory
    fn load_dir_recursive(fixture: &mut Self, base_path: &Path, current_path: &Path) -> Result<()> {
        for entry in fs::read_dir(current_path)? {
            let entry = entry?;
            let path = entry.path();

            if path.is_dir() {
                // Recursively process subdirectories
                Self::load_dir_recursive(fixture, base_path, &path)?;
            } else if path.is_file() && path.extension().is_some_and(|ext| ext == "rs") {
                // Read file contents
                let contents = fs::read_to_string(&path)?;

                // Get relative path from base
                let relative_path = path
                    .strip_prefix(base_path)
                    .unwrap_or(&path)
                    .to_string_lossy()
                    .to_string();

                fixture.add_file(&relative_path, &contents)?;
            }
        }

        Ok(())
    }

    /// Parse a file using its cached contents from the database
    ///
    /// # Errors
    ///
    /// Returns an error if file contents cannot be retrieved
    pub fn parse_file(&self, file: SourceFile) -> Result<rv_parser::ParseResult> {
        let contents = self.db.get_file_contents(file)?;
        Ok(rv_parser::parse_source(&contents))
    }
}

impl Default for TestFixture {
    fn default() -> Self {
        Self::new()
    }
}
