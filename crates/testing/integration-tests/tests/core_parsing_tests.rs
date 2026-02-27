//! Tests for parsing Rust's core library
//!
//! Phase 6: Testing with `core` source code

use lang_raven::RavenLanguage;
use rv_hir_lower::lower_source_file;
use rv_syntax::Language;
use std::path::Path;

const RUST_SRC_PATH: &str = "/tmp/rust-src/library/core/src";

fn parse_file(path: &Path) -> ParseResult {
    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            return ParseResult {
                success: false,
                tree_sitter_errors: 0,
                hir_functions: 0,
                hir_structs: 0,
                hir_enums: 0,
                hir_traits: 0,
                hir_impl_blocks: 0,
                error_message: Some(format!("Failed to read file: {e}")),
            }
        }
    };

    let language = RavenLanguage::new();

    // Parse with tree-sitter
    let tree = match language.parse(&source) {
        Ok(t) => t,
        Err(e) => {
            return ParseResult {
                success: false,
                tree_sitter_errors: 0,
                hir_functions: 0,
                hir_structs: 0,
                hir_enums: 0,
                hir_traits: 0,
                hir_impl_blocks: 0,
                error_message: Some(format!("Parse error: {e}")),
            }
        }
    };

    // Count tree-sitter errors
    let mut tree_sitter_errors = 0;
    let mut cursor = tree.walk();
    count_errors(&mut cursor, &mut tree_sitter_errors);

    // Try to lower to HIR - use catch_unwind to avoid panics stopping the test
    let root = language.lower_node(&tree.root_node(), &source);
    let hir_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        lower_source_file(&root)
    }));

    match hir_result {
        Ok(hir) => ParseResult {
            success: tree_sitter_errors == 0,
            tree_sitter_errors,
            hir_functions: hir.functions.len(),
            hir_structs: hir.structs.len(),
            hir_enums: hir.enums.len(),
            hir_traits: hir.traits.len(),
            hir_impl_blocks: hir.impl_blocks.len(),
            error_message: None,
        },
        Err(e) => {
            let msg = if let Some(s) = e.downcast_ref::<&str>() {
                s.to_string()
            } else if let Some(s) = e.downcast_ref::<String>() {
                s.clone()
            } else {
                "Unknown panic".to_string()
            };
            ParseResult {
                success: false,
                tree_sitter_errors,
                hir_functions: 0,
                hir_structs: 0,
                hir_enums: 0,
                hir_traits: 0,
                hir_impl_blocks: 0,
                error_message: Some(msg),
            }
        }
    }
}

fn count_errors(cursor: &mut tree_sitter::TreeCursor, count: &mut usize) {
    loop {
        if cursor.node().is_error() || cursor.node().is_missing() {
            *count += 1;
        }

        if cursor.goto_first_child() {
            count_errors(cursor, count);
            cursor.goto_parent();
        }

        if !cursor.goto_next_sibling() {
            break;
        }
    }
}

#[derive(Debug)]
struct ParseResult {
    success: bool,
    tree_sitter_errors: usize,
    hir_functions: usize,
    hir_structs: usize,
    hir_enums: usize,
    hir_traits: usize,
    hir_impl_blocks: usize,
    error_message: Option<String>,
}

#[test]
fn test_parse_core_unit() {
    let path = Path::new(RUST_SRC_PATH).join("unit.rs");
    if !path.exists() {
        eprintln!("Skipping test: Rust source not found at {}", path.display());
        return;
    }

    let result = parse_file(&path);
    println!("unit.rs: {:?}", result);

    // unit.rs has 1 impl block
    assert!(result.hir_impl_blocks >= 1, "Expected at least 1 impl block");
}

#[test]
fn test_parse_core_marker() {
    let path = Path::new(RUST_SRC_PATH).join("marker.rs");
    if !path.exists() {
        eprintln!("Skipping test: Rust source not found at {}", path.display());
        return;
    }

    let result = parse_file(&path);
    println!("marker.rs: {:?}", result);
    println!("  tree-sitter errors: {}", result.tree_sitter_errors);
    println!("  functions: {}", result.hir_functions);
    println!("  structs: {}", result.hir_structs);
    println!("  traits: {}", result.hir_traits);
    println!("  impl blocks: {}", result.hir_impl_blocks);

    // marker.rs contains Copy, Clone, Send, Sync traits
    // We expect some items to be parsed
}

#[test]
fn test_parse_core_option() {
    let path = Path::new(RUST_SRC_PATH).join("option.rs");
    if !path.exists() {
        eprintln!("Skipping test: Rust source not found at {}", path.display());
        return;
    }

    let result = parse_file(&path);
    println!("option.rs: {:?}", result);
    println!("  tree-sitter errors: {}", result.tree_sitter_errors);
    println!("  functions: {}", result.hir_functions);
    println!("  structs: {}", result.hir_structs);
    println!("  enums: {}", result.hir_enums);
    println!("  traits: {}", result.hir_traits);
    println!("  impl blocks: {}", result.hir_impl_blocks);

    // option.rs should have the Option enum
    assert!(result.hir_enums >= 1, "Expected Option enum");
}

#[test]
fn test_parse_core_result() {
    let path = Path::new(RUST_SRC_PATH).join("result.rs");
    if !path.exists() {
        eprintln!("Skipping test: Rust source not found at {}", path.display());
        return;
    }

    let result = parse_file(&path);
    println!("result.rs: {:?}", result);
    println!("  tree-sitter errors: {}", result.tree_sitter_errors);
    println!("  functions: {}", result.hir_functions);
    println!("  enums: {}", result.hir_enums);
    println!("  traits: {}", result.hir_traits);
    println!("  impl blocks: {}", result.hir_impl_blocks);

    // result.rs should have the Result enum
    assert!(result.hir_enums >= 1, "Expected Result enum");
}

#[test]
fn test_parse_all_core_files() {
    let core_path = Path::new(RUST_SRC_PATH);
    if !core_path.exists() {
        eprintln!(
            "Skipping test: Rust source not found at {}",
            core_path.display()
        );
        return;
    }

    let mut total_files = 0;
    let mut successful_files = 0;
    let mut total_ts_errors = 0;
    let mut total_functions = 0;
    let mut total_structs = 0;
    let mut total_enums = 0;
    let mut total_traits = 0;
    let mut total_impl_blocks = 0;
    let mut failed_files: Vec<(String, usize, Option<String>)> = Vec::new();

    // Parse all .rs files in core/src
    for entry in std::fs::read_dir(core_path).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "rs") {
            total_files += 1;
            let result = parse_file(&path);

            if result.success && result.error_message.is_none() {
                successful_files += 1;
            } else {
                failed_files.push((
                    path.file_name().unwrap().to_string_lossy().to_string(),
                    result.tree_sitter_errors,
                    result.error_message,
                ));
            }

            total_ts_errors += result.tree_sitter_errors;
            total_functions += result.hir_functions;
            total_structs += result.hir_structs;
            total_enums += result.hir_enums;
            total_traits += result.hir_traits;
            total_impl_blocks += result.hir_impl_blocks;
        }
    }

    println!("\n=== Core Library Parsing Summary ===");
    println!("Total files: {}", total_files);
    println!(
        "Successfully parsed (no errors): {}/{}",
        successful_files, total_files
    );
    println!("Total tree-sitter errors: {}", total_ts_errors);
    println!("\nHIR Items extracted:");
    println!("  Functions: {}", total_functions);
    println!("  Structs: {}", total_structs);
    println!("  Enums: {}", total_enums);
    println!("  Traits: {}", total_traits);
    println!("  Impl blocks: {}", total_impl_blocks);

    if !failed_files.is_empty() {
        println!("\nFiles with tree-sitter errors:");
        for (file, errors, _) in &failed_files {
            if *errors > 0 {
                println!("  {} ({} errors)", file, errors);
            }
        }

        println!("\nFiles with HIR lowering errors (ICE):");
        for (file, _, err_msg) in &failed_files {
            if let Some(msg) = err_msg {
                // Truncate long error messages
                let short_msg: String = msg.chars().take(100).collect();
                println!("  {}: {}", file, short_msg);
            }
        }
    }

    // Report summary but don't fail - this is exploratory testing
    println!("\n=== Summary ===");
    println!(
        "Core library parsing: {}/{} files successful",
        successful_files, total_files
    );
}
