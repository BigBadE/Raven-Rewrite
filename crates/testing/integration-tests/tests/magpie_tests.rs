//! Integration tests using Magpie package manager
//!
//! This test suite runs all test projects in the test-projects directory
//! using Magpie's test command.

use std::fs;
use std::path::PathBuf;

// Import magpie backend directly
use magpie::backend::Backend;
use magpie::backends::{CraneliftBackend, LLVMBackend, RavenBackend};
use magpie::manifest::Manifest;

#[test]
fn test_all_projects() {
    let test_projects_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("test-projects");

    // Read all project directories
    let mut projects = Vec::new();
    for entry in fs::read_dir(&test_projects_dir)
        .expect("Failed to read test-projects directory")
    {
        let entry = entry.expect("Failed to read directory entry");
        let path = entry.path();

        if path.is_dir() {
            // Check if it has a Cargo.toml
            if path.join("Cargo.toml").exists() {
                projects.push(path);
            }
        }
    }

    // Sort projects by name for consistent ordering
    projects.sort();

    assert!(
        !projects.is_empty(),
        "No test projects found in {:?}",
        test_projects_dir
    );

    let mut total_passed = 0;
    let mut total_failed = 0;
    let mut failed_projects = Vec::new();

    for project_path in &projects {
        let project_name = project_path
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown");

        println!("\n==== Testing project: {} ====", project_name);

        // Load manifest
        let manifest = match Manifest::find_in_dir(project_path) {
            Ok(m) => m,
            Err(e) => {
                eprintln!("Failed to load manifest for {}: {}", project_name, e);
                failed_projects.push(project_name.to_string());
                continue;
            }
        };

        // Test with interpreter backend
        println!("\n  -- Interpreter Backend --");
        let backend = RavenBackend::new();
        match backend.test(&manifest, project_path) {
            Ok(result) => {
                for message in &result.messages {
                    println!("{}", message);
                }

                total_passed += result.passed;
                total_failed += result.failed;

                if !result.success {
                    failed_projects.push(format!("{} (interpreter)", project_name));
                }
            }
            Err(e) => {
                eprintln!("Failed to run tests for {}: {}", project_name, e);
                failed_projects.push(format!("{} (interpreter)", project_name));
            }
        }

        // Test with JIT backend
        println!("\n  -- JIT Backend --");
        let backend = match CraneliftBackend::new() {
            Ok(b) => b,
            Err(e) => {
                eprintln!("Failed to create JIT backend: {}", e);
                failed_projects.push(format!("{} (jit)", project_name));
                continue;
            }
        };
        match backend.test(&manifest, project_path) {
            Ok(result) => {
                for message in &result.messages {
                    println!("{}", message);
                }

                total_passed += result.passed;
                total_failed += result.failed;

                if !result.success {
                    failed_projects.push(format!("{} (jit)", project_name));
                }
            }
            Err(e) => {
                eprintln!("Failed to run tests for {}: {}", project_name, e);
                failed_projects.push(format!("{} (jit)", project_name));
            }
        }

        // Test with LLVM backend
        println!("\n  -- LLVM Backend --");
        let backend = match LLVMBackend::new() {
            Ok(b) => b,
            Err(e) => {
                eprintln!("Failed to create LLVM backend: {}", e);
                failed_projects.push(format!("{} (llvm)", project_name));
                continue;
            }
        };
        match backend.test(&manifest, project_path) {
            Ok(result) => {
                for message in &result.messages {
                    println!("{}", message);
                }

                total_passed += result.passed;
                total_failed += result.failed;

                if !result.success {
                    failed_projects.push(format!("{} (llvm)", project_name));
                }
            }
            Err(e) => {
                eprintln!("Failed to run tests for {}: {}", project_name, e);
                failed_projects.push(format!("{} (llvm)", project_name));
            }
        }
    }

    println!("\n==== Summary ====");
    println!("Total projects tested: {}", projects.len());
    println!("Total tests passed: {}", total_passed);
    println!("Total tests failed: {}", total_failed);

    if !failed_projects.is_empty() {
        panic!(
            "Some projects had failing tests: {:?}",
            failed_projects
        );
    }

    assert_eq!(
        total_failed, 0,
        "Expected all tests to pass, but {} failed",
        total_failed
    );
}
