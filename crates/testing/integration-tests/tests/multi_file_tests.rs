//! Multi-file integration tests
//!
//! These tests verify the multi-file test infrastructure and demonstrate
//! the module system capabilities. Note that actual compilation and execution
//! of multi-file projects is deferred to when the full module system is
//! integrated with the compiler pipeline.

use integration_tests::multi_file::{self, TestResult};

/// Test 16: Basic multi-file modules
///
/// Tests a simple two-file project with module imports
#[test]
fn test_16_multi_file_modules() {
    let project = multi_file::test_16_multi_file_modules();
    match project.run() {
        TestResult::Pass => {}
        TestResult::Fail { reason } => panic!("Test 16 failed: {}", reason),
    }
}

/// Test 17: Module hierarchy
///
/// Tests a three-level module hierarchy with nested modules
#[test]
fn test_17_module_hierarchy() {
    let project = multi_file::test_17_module_hierarchy();
    match project.run() {
        TestResult::Pass => {}
        TestResult::Fail { reason } => panic!("Test 17 failed: {}", reason),
    }
}

/// Test 18: Use declarations
///
/// Tests `use` declarations for importing constants from submodules
#[test]
fn test_18_use_declarations() {
    let project = multi_file::test_18_use_declarations();
    match project.run() {
        TestResult::Pass => {}
        TestResult::Fail { reason } => panic!("Test 18 failed: {}", reason),
    }
}

/// Test 19: Large codebase
///
/// Tests a generated codebase with 10 modules and 50 functions
#[test]
fn test_19_large_codebase() {
    let project = multi_file::test_19_large_codebase();
    match project.run() {
        TestResult::Pass => {}
        TestResult::Fail { reason } => panic!("Test 19 failed: {}", reason),
    }
}
