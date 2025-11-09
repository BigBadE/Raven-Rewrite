//! Backend trait for different package manager implementations

use crate::manifest::Manifest;
use anyhow::Result;
use std::path::Path;

/// Package manager backend trait
pub trait Backend {
    /// Build the project
    fn build(&self, manifest: &Manifest, project_dir: &Path) -> Result<BuildResult>;

    /// Run the project
    fn run(&self, manifest: &Manifest, project_dir: &Path, args: &[String]) -> Result<()>;

    /// Test the project
    fn test(&self, manifest: &Manifest, project_dir: &Path) -> Result<TestResult>;

    /// Check the project (validate without building)
    fn check(&self, manifest: &Manifest, project_dir: &Path) -> Result<()>;

    /// Clean build artifacts
    fn clean(&self, project_dir: &Path) -> Result<()>;
}

/// Build result
#[derive(Debug, Clone)]
pub struct BuildResult {
    /// Whether the build succeeded
    pub success: bool,

    /// Build output messages
    pub messages: Vec<String>,

    /// Path to the built executable (if any)
    pub executable: Option<std::path::PathBuf>,
}

/// Test result
#[derive(Debug, Clone)]
pub struct TestResult {
    /// Whether all tests passed
    pub success: bool,

    /// Number of tests passed
    pub passed: usize,

    /// Number of tests failed
    pub failed: usize,

    /// Test output messages
    pub messages: Vec<String>,
}
