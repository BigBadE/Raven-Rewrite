//! Tests for compiling and using the real Rust core library
//!
//! This test suite attempts to compile actual Rust core library modules
//! and tracks what features are missing or broken.

use lang_raven::RavenLanguage;
use rv_hir_lower::lower_source_file;
use rv_syntax::Language;
use std::collections::HashMap;
use std::path::Path;

/// Get the Rust source path from rustup sysroot
fn get_rust_src_path() -> Option<std::path::PathBuf> {
    // Try to get sysroot from rustc
    let output = std::process::Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .ok()?;

    let sysroot = String::from_utf8(output.stdout).ok()?;
    let sysroot = sysroot.trim();

    let path = std::path::Path::new(sysroot)
        .join("lib/rustlib/src/rust/library/core/src");

    if path.exists() {
        Some(path)
    } else {
        None
    }
}

const RUST_SRC_PATH: &str = "/home/ethan/.rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src";

/// Result of attempting to compile a core library file
#[derive(Debug)]
struct CompileResult {
    file_name: String,
    /// Tree-sitter parsing phase
    parse_success: bool,
    parse_errors: usize,
    /// HIR lowering phase
    hir_success: bool,
    hir_error: Option<String>,
    /// HIR statistics
    hir_functions: usize,
    hir_structs: usize,
    hir_enums: usize,
    hir_traits: usize,
    hir_impl_blocks: usize,
    hir_type_aliases: usize,
    hir_modules: usize,
    hir_use_items: usize,
    hir_external_functions: usize,
    hir_statics: usize,
    hir_consts: usize,
}

/// Categorized error tracking
#[derive(Debug, Default)]
struct ErrorCategories {
    /// Errors related to macro invocations
    macro_errors: Vec<(String, String)>,
    /// Errors related to unsupported syntax
    syntax_errors: Vec<(String, String)>,
    /// Errors related to type parsing
    type_errors: Vec<(String, String)>,
    /// Errors related to patterns
    pattern_errors: Vec<(String, String)>,
    /// Errors related to attributes
    attribute_errors: Vec<(String, String)>,
    /// Other/uncategorized errors
    other_errors: Vec<(String, String)>,
}

impl ErrorCategories {
    fn categorize(&mut self, file: &str, error: &str) {
        let error_lower = error.to_lowercase();
        if error_lower.contains("macro")
            || error_lower.contains("!") && error_lower.contains("invocation")
        {
            self.macro_errors.push((file.to_string(), error.to_string()));
        } else if error_lower.contains("syntax")
            || error_lower.contains("unexpected")
            || error_lower.contains("expected")
        {
            self.syntax_errors
                .push((file.to_string(), error.to_string()));
        } else if error_lower.contains("type") || error_lower.contains("generic") {
            self.type_errors.push((file.to_string(), error.to_string()));
        } else if error_lower.contains("pattern") || error_lower.contains("match") {
            self.pattern_errors
                .push((file.to_string(), error.to_string()));
        } else if error_lower.contains("attribute") || error_lower.contains("#[") {
            self.attribute_errors
                .push((file.to_string(), error.to_string()));
        } else {
            self.other_errors
                .push((file.to_string(), error.to_string()));
        }
    }

    fn print_summary(&self) {
        println!("\n=== Error Categories ===");
        println!("Macro errors: {}", self.macro_errors.len());
        println!("Syntax errors: {}", self.syntax_errors.len());
        println!("Type errors: {}", self.type_errors.len());
        println!("Pattern errors: {}", self.pattern_errors.len());
        println!("Attribute errors: {}", self.attribute_errors.len());
        println!("Other errors: {}", self.other_errors.len());
    }
}

fn count_tree_sitter_errors(cursor: &mut tree_sitter::TreeCursor) -> usize {
    let mut count = 0;
    loop {
        if cursor.node().is_error() || cursor.node().is_missing() {
            count += 1;
        }

        if cursor.goto_first_child() {
            count += count_tree_sitter_errors(cursor);
            cursor.goto_parent();
        }

        if !cursor.goto_next_sibling() {
            break;
        }
    }
    count
}

fn compile_file(path: &Path) -> CompileResult {
    let file_name = path
        .file_name()
        .map(|n| n.to_string_lossy().to_string())
        .unwrap_or_default();

    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            return CompileResult {
                file_name,
                parse_success: false,
                parse_errors: 0,
                hir_success: false,
                hir_error: Some(format!("Failed to read file: {e}")),
                hir_functions: 0,
                hir_structs: 0,
                hir_enums: 0,
                hir_traits: 0,
                hir_impl_blocks: 0,
                hir_type_aliases: 0,
                hir_modules: 0,
                hir_use_items: 0,
                hir_external_functions: 0,
                hir_statics: 0,
                hir_consts: 0,
            }
        }
    };

    let language = RavenLanguage::new();

    // Phase 1: Parse with tree-sitter
    let tree = match language.parse(&source) {
        Ok(t) => t,
        Err(e) => {
            return CompileResult {
                file_name,
                parse_success: false,
                parse_errors: 0,
                hir_success: false,
                hir_error: Some(format!("Tree-sitter parse error: {e}")),
                hir_functions: 0,
                hir_structs: 0,
                hir_enums: 0,
                hir_traits: 0,
                hir_impl_blocks: 0,
                hir_type_aliases: 0,
                hir_modules: 0,
                hir_use_items: 0,
                hir_external_functions: 0,
                hir_statics: 0,
                hir_consts: 0,
            }
        }
    };

    let mut cursor = tree.walk();
    let parse_errors = count_tree_sitter_errors(&mut cursor);
    let parse_success = parse_errors == 0;

    // Phase 2: Convert to generic syntax tree
    let root = language.lower_node(&tree.root_node(), &source);

    // Phase 3: Lower to HIR
    let hir_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        lower_source_file(&root)
    }));

    match hir_result {
        Ok(hir) => CompileResult {
            file_name,
            parse_success,
            parse_errors,
            hir_success: true,
            hir_error: None,
            hir_functions: hir.functions.len(),
            hir_structs: hir.structs.len(),
            hir_enums: hir.enums.len(),
            hir_traits: hir.traits.len(),
            hir_impl_blocks: hir.impl_blocks.len(),
            hir_type_aliases: hir.type_aliases.len(),
            hir_modules: hir.modules.len(),
            hir_use_items: hir.use_items.len(),
            hir_external_functions: hir.external_functions.len(),
            hir_statics: hir.static_items.len(),
            hir_consts: hir.const_items.len(),
        },
        Err(e) => {
            let error_msg = if let Some(s) = e.downcast_ref::<&str>() {
                s.to_string()
            } else if let Some(s) = e.downcast_ref::<String>() {
                s.clone()
            } else {
                "Unknown panic during HIR lowering".to_string()
            };
            CompileResult {
                file_name,
                parse_success,
                parse_errors,
                hir_success: false,
                hir_error: Some(error_msg),
                hir_functions: 0,
                hir_structs: 0,
                hir_enums: 0,
                hir_traits: 0,
                hir_impl_blocks: 0,
                hir_type_aliases: 0,
                hir_modules: 0,
                hir_use_items: 0,
                hir_external_functions: 0,
                hir_statics: 0,
                hir_consts: 0,
            }
        }
    }
}

#[test]
fn test_compile_core_option() {
    let path = Path::new(RUST_SRC_PATH).join("option.rs");
    if !path.exists() {
        eprintln!("Skipping test: Rust source not found at {}", path.display());
        eprintln!("To run this test, install rust-src:");
        eprintln!("  rustup component add rust-src");
        eprintln!("  cp -r ~/.rustup/toolchains/*/lib/rustlib/src/rust/library /tmp/rust-src");
        return;
    }

    let result = compile_file(&path);

    println!("\n=== core::option Compilation Result ===");
    println!("File: {}", result.file_name);
    println!("Parse success: {} ({} errors)", result.parse_success, result.parse_errors);
    println!("HIR success: {}", result.hir_success);
    if let Some(ref err) = result.hir_error {
        println!("HIR error: {}", err);
    }
    println!("\nHIR Statistics:");
    println!("  Functions: {}", result.hir_functions);
    println!("  Structs: {}", result.hir_structs);
    println!("  Enums: {}", result.hir_enums);
    println!("  Traits: {}", result.hir_traits);
    println!("  Impl blocks: {}", result.hir_impl_blocks);
    println!("  Type aliases: {}", result.hir_type_aliases);
    println!("  Modules: {}", result.hir_modules);
    println!("  Use items: {}", result.hir_use_items);
    println!("  External functions: {}", result.hir_external_functions);
    println!("  Statics: {}", result.hir_statics);
    println!("  Consts: {}", result.hir_consts);

    // The test should eventually pass - for now we're tracking progress
    if !result.hir_success {
        println!("\n[TRACKING] core::option not yet fully compiling");
    }
}

#[test]
fn test_compile_core_result() {
    let path = Path::new(RUST_SRC_PATH).join("result.rs");
    if !path.exists() {
        eprintln!("Skipping test: Rust source not found");
        return;
    }

    let result = compile_file(&path);

    println!("\n=== core::result Compilation Result ===");
    println!("File: {}", result.file_name);
    println!("Parse success: {} ({} errors)", result.parse_success, result.parse_errors);
    println!("HIR success: {}", result.hir_success);
    if let Some(ref err) = result.hir_error {
        println!("HIR error: {}", err);
    }
    println!("\nHIR Statistics:");
    println!("  Functions: {}", result.hir_functions);
    println!("  Enums: {}", result.hir_enums);
    println!("  Impl blocks: {}", result.hir_impl_blocks);
}

#[test]
fn test_compile_core_marker() {
    let path = Path::new(RUST_SRC_PATH).join("marker.rs");
    if !path.exists() {
        eprintln!("Skipping test: Rust source not found");
        return;
    }

    let result = compile_file(&path);

    println!("\n=== core::marker Compilation Result ===");
    println!("File: {}", result.file_name);
    println!("Parse success: {} ({} errors)", result.parse_success, result.parse_errors);
    println!("HIR success: {}", result.hir_success);
    if let Some(ref err) = result.hir_error {
        println!("HIR error: {}", err);
    }
    println!("\nHIR Statistics:");
    println!("  Traits: {}", result.hir_traits);
    println!("  Structs: {}", result.hir_structs);
    println!("  Impl blocks: {}", result.hir_impl_blocks);
}

#[test]
fn test_compile_core_clone() {
    let path = Path::new(RUST_SRC_PATH).join("clone.rs");
    if !path.exists() {
        eprintln!("Skipping test: Rust source not found");
        return;
    }

    let result = compile_file(&path);

    println!("\n=== core::clone Compilation Result ===");
    println!("Parse success: {} ({} errors)", result.parse_success, result.parse_errors);
    println!("HIR success: {}", result.hir_success);
    if let Some(ref err) = result.hir_error {
        println!("HIR error: {}", err);
    }
    println!("  Traits: {}", result.hir_traits);
    println!("  Impl blocks: {}", result.hir_impl_blocks);
}

#[test]
fn test_compile_core_cmp() {
    let path = Path::new(RUST_SRC_PATH).join("cmp.rs");
    if !path.exists() {
        eprintln!("Skipping test: Rust source not found");
        return;
    }

    let result = compile_file(&path);

    println!("\n=== core::cmp Compilation Result ===");
    println!("Parse success: {} ({} errors)", result.parse_success, result.parse_errors);
    println!("HIR success: {}", result.hir_success);
    if let Some(ref err) = result.hir_error {
        println!("HIR error: {}", err);
    }
    println!("  Traits: {}", result.hir_traits);
    println!("  Enums: {}", result.hir_enums);
    println!("  Impl blocks: {}", result.hir_impl_blocks);
}

#[test]
fn test_compile_core_default() {
    let path = Path::new(RUST_SRC_PATH).join("default.rs");
    if !path.exists() {
        eprintln!("Skipping test: Rust source not found");
        return;
    }

    let result = compile_file(&path);

    println!("\n=== core::default Compilation Result ===");
    println!("Parse success: {} ({} errors)", result.parse_success, result.parse_errors);
    println!("HIR success: {}", result.hir_success);
    if let Some(ref err) = result.hir_error {
        println!("HIR error: {}", err);
    }
    println!("  Traits: {}", result.hir_traits);
    println!("  Impl blocks: {}", result.hir_impl_blocks);
}

#[test]
fn test_compile_all_core_files() {
    let core_path = Path::new(RUST_SRC_PATH);
    if !core_path.exists() {
        eprintln!(
            "Skipping test: Rust source not found at {}",
            core_path.display()
        );
        eprintln!("To run this test:");
        eprintln!("  rustup component add rust-src");
        eprintln!("  cp -r ~/.rustup/toolchains/*/lib/rustlib/src/rust/library /tmp/rust-src");
        return;
    }

    let mut results: Vec<CompileResult> = Vec::new();
    let mut error_categories = ErrorCategories::default();

    // Compile all .rs files in core/src
    for entry in std::fs::read_dir(core_path).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "rs") {
            let result = compile_file(&path);

            // Categorize any errors
            if let Some(ref err) = result.hir_error {
                error_categories.categorize(&result.file_name, err);
            }

            results.push(result);
        }
    }

    // Print summary
    let total = results.len();
    let parse_success = results.iter().filter(|r| r.parse_success).count();
    let hir_success = results.iter().filter(|r| r.hir_success).count();

    let total_functions: usize = results.iter().map(|r| r.hir_functions).sum();
    let total_structs: usize = results.iter().map(|r| r.hir_structs).sum();
    let total_enums: usize = results.iter().map(|r| r.hir_enums).sum();
    let total_traits: usize = results.iter().map(|r| r.hir_traits).sum();
    let total_impl_blocks: usize = results.iter().map(|r| r.hir_impl_blocks).sum();

    println!("\n========================================");
    println!("     RUST CORE LIBRARY COMPILATION     ");
    println!("========================================");
    println!();
    println!("Files processed: {}", total);
    println!(
        "Parse success:   {}/{} ({:.1}%)",
        parse_success,
        total,
        100.0 * parse_success as f64 / total as f64
    );
    println!(
        "HIR success:     {}/{} ({:.1}%)",
        hir_success,
        total,
        100.0 * hir_success as f64 / total as f64
    );
    println!();
    println!("Total HIR items extracted:");
    println!("  Functions:   {}", total_functions);
    println!("  Structs:     {}", total_structs);
    println!("  Enums:       {}", total_enums);
    println!("  Traits:      {}", total_traits);
    println!("  Impl blocks: {}", total_impl_blocks);

    error_categories.print_summary();

    // List files that failed HIR lowering
    println!("\n=== Files with HIR Failures ===");
    for result in results.iter().filter(|r| !r.hir_success) {
        println!(
            "  {} - {}",
            result.file_name,
            result
                .hir_error
                .as_ref()
                .map(|s| {
                    // Truncate long errors
                    if s.len() > 80 {
                        format!("{}...", &s[..80])
                    } else {
                        s.clone()
                    }
                })
                .unwrap_or_default()
        );
    }

    // List files that succeeded
    println!("\n=== Files Successfully Compiled to HIR ===");
    for result in results.iter().filter(|r| r.hir_success) {
        println!(
            "  {} (fn:{}, struct:{}, enum:{}, trait:{}, impl:{})",
            result.file_name,
            result.hir_functions,
            result.hir_structs,
            result.hir_enums,
            result.hir_traits,
            result.hir_impl_blocks
        );
    }
}

/// Test that we can use types from core after compilation
#[test]
fn test_use_compiled_core_option() {
    let path = Path::new(RUST_SRC_PATH).join("option.rs");
    if !path.exists() {
        eprintln!("Skipping test: Rust source not found");
        return;
    }

    let result = compile_file(&path);

    if result.hir_success {
        println!("\n=== Using Compiled core::option ===");
        println!("Option enum found: {}", result.hir_enums >= 1);
        println!("Impl blocks found: {}", result.hir_impl_blocks);
        println!("Functions found: {}", result.hir_functions);

        // TODO: Once compilation works, test actually using the Option type
        // by creating a test program that imports and uses core::option::Option
    } else {
        println!("\n[BLOCKED] Cannot use core::option - compilation failed");
        if let Some(ref err) = result.hir_error {
            println!("Error: {}", err);
        }
    }
}

/// Detailed analysis of what's blocking core::option compilation
#[test]
fn test_analyze_core_option_blockers() {
    let path = Path::new(RUST_SRC_PATH).join("option.rs");
    if !path.exists() {
        eprintln!("Skipping test: Rust source not found");
        return;
    }

    let source = std::fs::read_to_string(&path).unwrap();
    let language = RavenLanguage::new();
    let tree = language.parse(&source).unwrap();

    // Analyze the tree for unsupported constructs
    let mut unsupported: HashMap<String, usize> = HashMap::new();

    fn analyze_node(
        node: tree_sitter::Node,
        source: &str,
        unsupported: &mut HashMap<String, usize>,
    ) {
        let kind = node.kind();

        // Track potentially unsupported constructs
        match kind {
            "macro_invocation" => {
                // Get macro name
                if let Some(macro_node) = node.child_by_field_name("macro") {
                    let name = &source[macro_node.byte_range()];
                    *unsupported.entry(format!("macro:{}", name)).or_insert(0) += 1;
                } else {
                    *unsupported.entry("macro:unknown".to_string()).or_insert(0) += 1;
                }
            }
            "attribute_item" | "inner_attribute_item" => {
                // Get attribute content
                if let Some(attr) = node.child(1) {
                    let attr_text = &source[attr.byte_range()];
                    // Truncate long attributes
                    let short = if attr_text.len() > 30 {
                        &attr_text[..30]
                    } else {
                        attr_text
                    };
                    *unsupported
                        .entry(format!("attr:#[{}]", short))
                        .or_insert(0) += 1;
                }
            }
            "try_expression" => {
                *unsupported.entry("? operator".to_string()).or_insert(0) += 1;
            }
            "closure_expression" => {
                *unsupported.entry("closure".to_string()).or_insert(0) += 1;
            }
            "async_block" => {
                *unsupported.entry("async block".to_string()).or_insert(0) += 1;
            }
            "unsafe_block" => {
                *unsupported.entry("unsafe block".to_string()).or_insert(0) += 1;
            }
            "const_block" => {
                *unsupported.entry("const block".to_string()).or_insert(0) += 1;
            }
            "type_cast_expression" => {
                *unsupported.entry("type cast (as)".to_string()).or_insert(0) += 1;
            }
            _ => {}
        }

        // Recurse
        let mut cursor = node.walk();
        if cursor.goto_first_child() {
            loop {
                analyze_node(cursor.node(), source, unsupported);
                if !cursor.goto_next_sibling() {
                    break;
                }
            }
        }
    }

    analyze_node(tree.root_node(), &source, &mut unsupported);

    println!("\n=== core::option Feature Usage Analysis ===");
    println!("Constructs that may need support:\n");

    // Sort by count
    let mut items: Vec<_> = unsupported.iter().collect();
    items.sort_by(|a, b| b.1.cmp(a.1));

    for (construct, count) in items {
        println!("  {:40} {:>4} occurrences", construct, count);
    }
}
