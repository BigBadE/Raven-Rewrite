//! Comprehensive test suite using compiletest_rs (same framework as rustc).
//!
//! This test suite validates the Raven compiler's behavior across multiple dimensions:
//! - UI tests: Error message quality and diagnostics
//! - Compile-fail tests: Proper rejection of invalid programs
//! - Run-pass tests: Correct compilation and execution of valid programs
//! - Edge-cases: Complex scenarios and corner cases

use std::env;
use std::path::PathBuf;

/// Get the path to the magpie compiler binary.
///
/// This function looks for the magpie binary in the following order:
/// 1. `CARGO_BIN_EXE_magpie` environment variable (set by cargo test)
/// 2. `target/debug/magpie` (default debug build location)
/// 3. `magpie` (assume it's in PATH)
fn get_compiler_path() -> PathBuf {
    if let Ok(path) = env::var("CARGO_BIN_EXE_magpie") {
        return PathBuf::from(path);
    }

    let debug_path = PathBuf::from("target/debug/magpie");
    if debug_path.exists() {
        return debug_path;
    }

    PathBuf::from("magpie")
}

/// Run UI tests which validate error messages and compiler diagnostics.
///
/// Each test file should have a corresponding `.stderr` file with expected output.
/// Use `//~ ERROR` annotations in test files to mark expected error locations.
#[test]
fn run_ui_tests() {
    let mut config = compiletest_rs::Config::default();

    config.mode = compiletest_rs::common::Mode::Ui;
    config.src_base = PathBuf::from("tests/ui");
    config.build_base = PathBuf::from("target/compiletest");
    config.rustc_path = get_compiler_path();
    config.target_rustcflags = None;
    config.link_deps();
    config.clean_rmeta();

    compiletest_rs::run_tests(&config);
}

/// Run compile-fail tests which verify that invalid programs are properly rejected.
///
/// These tests ensure the compiler correctly enforces language semantics and
/// catches errors like trait bound violations, visibility errors, and constraint failures.
#[test]
fn run_compile_fail_tests() {
    let mut config = compiletest_rs::Config::default();

    config.mode = compiletest_rs::common::Mode::CompileFail;
    config.src_base = PathBuf::from("tests/compile-fail");
    config.build_base = PathBuf::from("target/compiletest");
    config.rustc_path = get_compiler_path();

    compiletest_rs::run_tests(&config);
}

/// Run run-pass tests which verify that valid programs compile and execute correctly.
///
/// These tests validate that the compiler correctly handles all implemented language
/// features and that the generated code executes as expected.
#[test]
fn run_run_pass_tests() {
    let mut config = compiletest_rs::Config::default();

    config.mode = compiletest_rs::common::Mode::RunPass;
    config.src_base = PathBuf::from("tests/run-pass");
    config.build_base = PathBuf::from("target/compiletest");
    config.rustc_path = get_compiler_path();

    compiletest_rs::run_tests(&config);
}

/// Run edge-case tests which validate complex scenarios and corner cases.
///
/// These tests ensure the compiler handles:
/// - Deeply nested generics
/// - Complex pattern matching
/// - Recursive types
/// - Closure captures
/// - Associated types
#[test]
fn run_edge_case_tests() {
    let mut config = compiletest_rs::Config::default();

    config.mode = compiletest_rs::common::Mode::RunPass;
    config.src_base = PathBuf::from("tests/edge-cases");
    config.build_base = PathBuf::from("target/compiletest");
    config.rustc_path = get_compiler_path();

    compiletest_rs::run_tests(&config);
}
