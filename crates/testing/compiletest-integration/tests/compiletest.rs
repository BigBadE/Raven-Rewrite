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
    // Try workspace root (../../.. from test directory)
    let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .and_then(|p| p.parent())
        .map(|p| p.to_path_buf())
        .expect("Failed to find workspace root");

    // Use the rustc-compat wrapper script that adds "compile" subcommand
    let wrapper_path = workspace_root.join("target/debug/magpie-rustc-compat");
    if wrapper_path.exists() {
        return wrapper_path;
    }

    // Fallback to direct magpie binary
    let debug_path = workspace_root.join("target/debug/magpie");
    if debug_path.exists() {
        return debug_path;
    }

    // Fallback to relative path
    let relative_path = PathBuf::from("target/debug/magpie-rustc-compat");
    if relative_path.exists() {
        return relative_path;
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

    // Use absolute path for build_base to avoid path resolution issues
    let build_base = std::env::current_dir()
        .expect("Failed to get current directory")
        .join("target/compiletest");
    config.build_base = build_base;

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
