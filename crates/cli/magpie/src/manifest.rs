//! Manifest parsing for package configuration files

use anyhow::{Context, Result};
use indexmap::IndexMap;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

/// Package manifest (e.g., Cargo.toml)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Manifest {
    /// Package metadata
    pub package: Package,

    /// Dependencies
    #[serde(default)]
    pub dependencies: IndexMap<String, Dependency>,

    /// Development dependencies
    #[serde(default, rename = "dev-dependencies")]
    pub dev_dependencies: IndexMap<String, Dependency>,

    /// Build dependencies
    #[serde(default, rename = "build-dependencies")]
    pub build_dependencies: IndexMap<String, Dependency>,

    /// Binary targets
    #[serde(default)]
    pub bin: Vec<BinTarget>,

    /// Library target
    #[serde(default)]
    pub lib: Option<LibTarget>,
}

/// Package metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Package {
    /// Package name
    pub name: String,

    /// Package version
    pub version: String,

    /// Edition (e.g., "2021", "2024")
    #[serde(default = "default_edition")]
    pub edition: String,

    /// Authors
    #[serde(default)]
    pub authors: Vec<String>,

    /// License
    #[serde(default)]
    pub license: Option<String>,

    /// Description
    #[serde(default)]
    pub description: Option<String>,
}

fn default_edition() -> String {
    "2024".to_string()
}

/// Dependency specification
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Dependency {
    /// Simple version string
    Simple(String),

    /// Detailed dependency
    Detailed(DetailedDependency),
}

/// Detailed dependency specification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetailedDependency {
    /// Version requirement
    #[serde(default)]
    pub version: Option<String>,

    /// Path to local dependency
    #[serde(default)]
    pub path: Option<PathBuf>,

    /// Git repository URL
    #[serde(default)]
    pub git: Option<String>,

    /// Git branch
    #[serde(default)]
    pub branch: Option<String>,

    /// Git tag
    #[serde(default)]
    pub tag: Option<String>,

    /// Git revision
    #[serde(default)]
    pub rev: Option<String>,

    /// Features to enable
    #[serde(default)]
    pub features: Vec<String>,

    /// Whether this is optional
    #[serde(default)]
    pub optional: bool,
}

/// Binary target
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BinTarget {
    /// Binary name
    pub name: String,

    /// Path to source file
    #[serde(default = "default_bin_path")]
    pub path: PathBuf,
}

fn default_bin_path() -> PathBuf {
    PathBuf::from("src/main.rs")
}

/// Library target
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LibTarget {
    /// Library name (defaults to package name)
    #[serde(default)]
    pub name: Option<String>,

    /// Path to source file
    #[serde(default = "default_lib_path")]
    pub path: PathBuf,
}

fn default_lib_path() -> PathBuf {
    PathBuf::from("src/lib.rs")
}

impl Manifest {
    /// Load manifest from a file
    pub fn from_file(path: &Path) -> Result<Self> {
        let contents = std::fs::read_to_string(path)
            .with_context(|| format!("Failed to read manifest file: {}", path.display()))?;

        toml::from_str(&contents)
            .with_context(|| format!("Failed to parse manifest file: {}", path.display()))
    }

    /// Find manifest in a directory (looks for Cargo.toml)
    pub fn find_in_dir(dir: &Path) -> Result<Self> {
        let manifest_path = dir.join("Cargo.toml");
        Self::from_file(&manifest_path)
    }

    /// Get the main binary target
    pub fn main_bin(&self) -> Option<&BinTarget> {
        self.bin.first()
    }

    /// Get library target
    pub fn lib_target(&self) -> Option<&LibTarget> {
        self.lib.as_ref()
    }
}
