//! Multi-file test infrastructure for integration testing.
//!
//! This module provides a framework for creating and testing multi-file projects,
//! including module systems, use declarations, and large codebases.

use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use tempfile::TempDir;

/// Result of running a multi-file test
#[derive(Debug)]
pub enum TestResult {
    /// Test passed successfully
    Pass,
    /// Test failed with a reason
    Fail { reason: String },
}

/// Expected result from a multi-file test
#[derive(Debug, Clone)]
pub enum ExpectedResult {
    /// Test should compile and run successfully with the given output
    Success { output: String },
    /// Test should fail with compilation errors matching the given patterns
    CompileError { patterns: Vec<String> },
}

/// A multi-file test project
///
/// This structure represents a complete test project with multiple source files,
/// expected results, and the ability to run the test and verify the outcome.
#[derive(Debug)]
pub struct MultiFileProject {
    /// Name of the test project
    pub name: String,
    /// Map of file paths to their contents
    pub files: HashMap<PathBuf, String>,
    /// Expected result from running the test
    pub expected: ExpectedResult,
}

impl MultiFileProject {
    /// Creates a new multi-file test project with the given name
    ///
    /// # Examples
    ///
    /// ```
    /// # use integration_tests::multi_file::MultiFileProject;
    /// let project = MultiFileProject::new("my-test-project");
    /// ```
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            files: HashMap::new(),
            expected: ExpectedResult::Success {
                output: String::new(),
            },
        }
    }

    /// Adds a file to the test project
    ///
    /// # Examples
    ///
    /// ```
    /// # use integration_tests::multi_file::MultiFileProject;
    /// let mut project = MultiFileProject::new("test");
    /// project.add_file("src/main.rs", "fn main() -> i64 { 42 }");
    /// ```
    pub fn add_file(&mut self, path: impl Into<PathBuf>, content: impl Into<String>) {
        self.files.insert(path.into(), content.into());
    }

    /// Sets the expected successful output for the test
    ///
    /// # Examples
    ///
    /// ```
    /// # use integration_tests::multi_file::MultiFileProject;
    /// let mut project = MultiFileProject::new("test");
    /// project.expect_success("42");
    /// ```
    pub fn expect_success(&mut self, output: impl Into<String>) {
        self.expected = ExpectedResult::Success {
            output: output.into(),
        };
    }

    /// Sets the expected compilation errors for the test
    ///
    /// # Examples
    ///
    /// ```
    /// # use integration_tests::multi_file::MultiFileProject;
    /// let mut project = MultiFileProject::new("test");
    /// project.expect_errors(vec!["undefined variable".to_string()]);
    /// ```
    pub fn expect_errors(&mut self, patterns: Vec<String>) {
        self.expected = ExpectedResult::CompileError { patterns };
    }

    /// Writes the multi-file test project to a temporary directory and verifies
    /// all files were created correctly.
    ///
    /// **Note:** This method only validates the file layout. It does not compile
    /// or execute the project because the multi-file compilation pipeline
    /// (module resolution across files via VFS) is not yet connected. Once
    /// `rv-resolve` supports cross-file module resolution, this method should
    /// be extended to invoke the compiler and check output/errors.
    ///
    /// # Returns
    ///
    /// Returns `TestResult::Pass` if all files were written and verified, or
    /// `TestResult::Fail` with a reason if file creation fails.
    #[must_use]
    pub fn run(&self) -> TestResult {
        let temp_dir = match TempDir::new() {
            Ok(dir) => dir,
            Err(e) => {
                return TestResult::Fail {
                    reason: format!("Failed to create temporary directory: {}", e),
                };
            }
        };

        let project_root = temp_dir.path().join(&self.name);

        if let Err(e) = fs::create_dir_all(&project_root) {
            return TestResult::Fail {
                reason: format!("Failed to create project root {:?}: {}", project_root, e),
            };
        }

        // Write all files to disk
        for (path, content) in &self.files {
            let full_path = project_root.join(path);

            if let Some(parent) = full_path.parent() {
                if let Err(e) = fs::create_dir_all(parent) {
                    return TestResult::Fail {
                        reason: format!("Failed to create directory {:?}: {}", parent, e),
                    };
                }
            }

            if let Err(e) = fs::write(&full_path, content) {
                return TestResult::Fail {
                    reason: format!("Failed to write file {:?}: {}", full_path, e),
                };
            }
        }

        // Verify all files exist on disk
        for path in self.files.keys() {
            let full_path = project_root.join(path);
            if !full_path.exists() {
                return TestResult::Fail {
                    reason: format!("File {:?} was not created", path),
                };
            }
        }

        TestResult::Pass
    }
}

/// Creates a new multi-file test project with the given name
///
/// This is a convenience function that wraps `MultiFileProject::new()`.
///
/// # Examples
///
/// ```
/// # use integration_tests::multi_file::create_project;
/// let project = create_project("my-test");
/// ```
#[must_use]
pub fn create_project(name: &str) -> MultiFileProject {
    MultiFileProject::new(name)
}

/// Test 16: Basic multi-file modules
///
/// Tests a simple two-file project where main.rs imports a function
/// from utils.rs and calls it.
#[must_use]
pub fn test_16_multi_file_modules() -> MultiFileProject {
    let mut project = create_project("16-multi-file-modules");

    project.add_file(
        "src/main.rs",
        r#"mod utils;

fn main() -> i64 {
    utils::get_value()
}
"#,
    );

    project.add_file(
        "src/utils.rs",
        r#"pub fn get_value() -> i64 {
    42
}
"#,
    );

    project.expect_success("42");
    project
}

/// Test 17: Module hierarchy
///
/// Tests a three-level module hierarchy: main -> math/mod.rs -> math/arithmetic.rs
#[must_use]
pub fn test_17_module_hierarchy() -> MultiFileProject {
    let mut project = create_project("17-module-hierarchy");

    project.add_file(
        "src/main.rs",
        r#"mod math;

fn main() -> i64 {
    math::arithmetic::add(40, 2)
}
"#,
    );

    project.add_file(
        "src/math/mod.rs",
        r#"pub mod arithmetic;
"#,
    );

    project.add_file(
        "src/math/arithmetic.rs",
        r#"pub fn add(a: i64, b: i64) -> i64 {
    a + b
}
"#,
    );

    project.expect_success("42");
    project
}

/// Test 18: Use declarations
///
/// Tests `use` declarations to import constants from submodules
#[must_use]
pub fn test_18_use_declarations() -> MultiFileProject {
    let mut project = create_project("18-use-declarations");

    project.add_file(
        "src/main.rs",
        r#"mod math;
use math::constants::ANSWER;

fn main() -> i64 {
    ANSWER
}
"#,
    );

    project.add_file(
        "src/math/mod.rs",
        r#"pub mod constants;
"#,
    );

    project.add_file(
        "src/math/constants.rs",
        r#"pub const ANSWER: i64 = 42;
"#,
    );

    project.expect_success("42");
    project
}

/// Test 19: Large codebase
///
/// Tests a generated codebase with 10 modules, each containing 5 functions.
/// This tests the compiler's ability to handle larger projects with many files.
#[must_use]
pub fn test_19_large_codebase() -> MultiFileProject {
    let mut project = create_project("19-large-codebase");

    // Generate main.rs with module declarations
    let mut main_content = String::new();
    for i in 0..10 {
        main_content.push_str(&format!("mod module_{};\n", i));
    }
    main_content.push_str("\nfn main() -> i64 {\n");
    main_content.push_str("    let mut sum = 0;\n");
    for i in 0..10 {
        for j in 0..5 {
            main_content.push_str(&format!("    sum = sum + module_{}::func_{}(sum);\n", i, j));
        }
    }
    main_content.push_str("    sum\n}\n");

    project.add_file("src/main.rs", main_content);

    // Generate 10 modules, each with 5 functions
    for mod_idx in 0..10 {
        let mut mod_content = String::new();

        for fn_idx in 0..5 {
            mod_content.push_str(&format!(
                "pub fn func_{}(x: i64) -> i64 {{\n    x + {}\n}}\n\n",
                fn_idx,
                mod_idx * 5 + fn_idx
            ));
        }

        project.add_file(format!("src/module_{}.rs", mod_idx), mod_content);
    }

    // Calculate the expected sum: each func_j in module_i adds (i*5 + j) to the
    // running total, applied cumulatively: sum = sum + (sum + increment).
    // Since file-layout verification doesn't execute code, the exact value doesn't
    // matter yet — but we compute it so the expectation is correct when compilation
    // is connected.
    let mut sum: i64 = 0;
    for mod_idx in 0..10_i64 {
        for fn_idx in 0..5_i64 {
            sum = sum + (sum + mod_idx * 5 + fn_idx);
        }
    }
    project.expect_success(&sum.to_string());
    project
}
