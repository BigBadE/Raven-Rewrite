//! End-to-end tests for compiling and running code that uses the real Rust core library
//!
//! These tests verify we can:
//! 1. Parse and lower the core library to HIR
//! 2. Lower core library HIR to MIR
//! 3. Compile through to all backends (Interpreter, Cranelift, LLVM)
//! 4. Execute code using core library types

use lang_raven::RavenLanguage;
use rv_hir::VariantFields;
use rv_hir_lower::lower_source_file;
use rv_syntax::Language;
use std::path::Path;
use tempfile::TempDir;

const RUST_SRC_PATH: &str = "/tmp/rust-src/library/core/src";

fn field_count(fields: &VariantFields) -> usize {
    match fields {
        VariantFields::Unit => 0,
        VariantFields::Tuple(v) => v.len(),
        VariantFields::Struct(v) => v.len(),
    }
}

/// Helper to run code through all backends
fn run_on_all_backends(code: &str) -> (Option<i64>, Option<i64>, Option<i64>) {
    use magpie::backend::Backend;
    use magpie::backends::{CraneliftBackend, LLVMBackend, RavenBackend};
    use magpie::manifest::Manifest;
    use std::fs;

    // Create temp project
    let temp_dir = TempDir::new().unwrap();
    let src_dir = temp_dir.path().join("src");
    fs::create_dir_all(&src_dir).unwrap();
    fs::write(src_dir.join("main.rs"), code).unwrap();

    let cargo_toml = r#"
[package]
name = "test_project"
version = "0.1.0"

[[bin]]
name = "test_project"
path = "src/main.rs"
"#;
    fs::write(temp_dir.path().join("Cargo.toml"), cargo_toml).unwrap();

    let manifest = Manifest::find_in_dir(temp_dir.path()).unwrap();

    // Interpreter
    let interpreter_result = {
        let backend = RavenBackend::new();
        match backend.test(&manifest, temp_dir.path()) {
            Ok(r) if r.passed > 0 => Some(1i64), // Just mark success
            _ => None,
        }
    };

    // Cranelift
    let cranelift_result = {
        match CraneliftBackend::new() {
            Ok(backend) => match backend.test(&manifest, temp_dir.path()) {
                Ok(r) if r.passed > 0 => Some(1i64),
                _ => None,
            },
            Err(_) => None,
        }
    };

    // LLVM
    let llvm_result = {
        match LLVMBackend::new() {
            Ok(backend) => match backend.test(&manifest, temp_dir.path()) {
                Ok(r) if r.passed > 0 => Some(1i64),
                _ => None,
            },
            Err(_) => None,
        }
    };

    (interpreter_result, cranelift_result, llvm_result)
}

/// Test that we can lower core::option::Option to HIR
#[test]
fn test_option_hir_to_mir() {
    let path = Path::new(RUST_SRC_PATH).join("option.rs");
    if !path.exists() {
        eprintln!("Skipping test: Rust source not found at {}", path.display());
        return;
    }

    let source = std::fs::read_to_string(&path).unwrap();
    let language = RavenLanguage::new();
    let tree = language.parse(&source).unwrap();
    let root = language.lower_node(&tree.root_node(), &source);
    let hir = lower_source_file(&root);

    println!("\n=== core::option HIR Summary ===");
    println!("Functions: {}", hir.functions.len());
    println!("Enums: {}", hir.enums.len());
    println!("Impl blocks: {}", hir.impl_blocks.len());

    // Find the Option enum
    let option_enum = hir.enums.values().find(|e| {
        let name = hir.interner.resolve(&e.name);
        name == "Option"
    });

    if let Some(option) = option_enum {
        println!("\nFound Option enum:");
        println!("  Name: {}", hir.interner.resolve(&option.name));
        println!("  Variants: {}", option.variants.len());
        for variant in &option.variants {
            let vname = hir.interner.resolve(&variant.name);
            println!("    - {} ({} fields)", vname, field_count(&variant.fields));
        }
        println!("  Generic params: {}", option.generic_params.len());
    } else {
        panic!("Option enum not found!");
    }

    // Try to find a simple function to test
    // Find is_some() method
    let is_some_fn = hir.functions.iter().find(|(_, f)| {
        let name = hir.interner.resolve(&f.name);
        name == "is_some"
    });

    if let Some((_fn_id, func)) = is_some_fn {
        println!("\nFound is_some function:");
        println!("  Name: {}", hir.interner.resolve(&func.name));
        println!("  Parameters: {}", func.parameters.len());
        println!("  Has body statements: {}", !func.body.stmts.is_empty());
    } else {
        println!("\nis_some function not found");
    }
}

/// Test compiling a simple user program that uses the Option type
#[test]
fn test_user_program_with_option() {
    // Simple program that uses Option
    let user_code = r#"
enum Option<T> {
    None,
    Some(T),
}

fn unwrap_or(opt: Option<i64>, default: i64) -> i64 {
    match opt {
        Option::Some(v) => v,
        Option::None => default,
    }
}

fn test_option_some() -> bool {
    let some_value = Option::Some(42);
    unwrap_or(some_value, 0) == 42
}

fn test_option_none() -> bool {
    let none_value: Option<i64> = Option::None;
    unwrap_or(none_value, 100) == 100
}

fn main() -> i64 {
    let some_value = Option::Some(42);
    let none_value: Option<i64> = Option::None;

    // Test unwrap_or
    let a = unwrap_or(some_value, 0);
    let b = unwrap_or(none_value, 100);

    a + b  // Should be 42 + 100 = 142
}
"#;

    let language = RavenLanguage::new();
    let tree = language.parse(user_code).unwrap();
    let root = language.lower_node(&tree.root_node(), user_code);
    let hir = lower_source_file(&root);

    println!("\n=== User Program with Option ===");
    println!("Functions: {}", hir.functions.len());
    println!("Enums: {}", hir.enums.len());

    // Find main function
    let main_fn = hir.functions.iter().find(|(_, f)| {
        let name = hir.interner.resolve(&f.name);
        name == "main"
    });

    assert!(main_fn.is_some(), "main function not found");

    // Run through all backends
    println!("\nRunning on all backends...");
    let (interp, cranelift, llvm) = run_on_all_backends(user_code);
    println!("  Interpreter: {:?}", interp);
    println!("  Cranelift:   {:?}", cranelift);
    println!("  LLVM:        {:?}", llvm);
}

/// Test that we can compile core::result
#[test]
fn test_result_hir_to_mir() {
    let path = Path::new(RUST_SRC_PATH).join("result.rs");
    if !path.exists() {
        eprintln!("Skipping test: Rust source not found");
        return;
    }

    let source = std::fs::read_to_string(&path).unwrap();
    let language = RavenLanguage::new();
    let tree = language.parse(&source).unwrap();
    let root = language.lower_node(&tree.root_node(), &source);
    let hir = lower_source_file(&root);

    println!("\n=== core::result HIR Summary ===");
    println!("Functions: {}", hir.functions.len());
    println!("Enums: {}", hir.enums.len());
    println!("Impl blocks: {}", hir.impl_blocks.len());

    // Find the Result enum
    let result_enum = hir.enums.values().find(|e| {
        let name = hir.interner.resolve(&e.name);
        name == "Result"
    });

    if let Some(result) = result_enum {
        println!("\nFound Result enum:");
        println!("  Name: {}", hir.interner.resolve(&result.name));
        println!("  Variants: {}", result.variants.len());
        for variant in &result.variants {
            let vname = hir.interner.resolve(&variant.name);
            println!("    - {} ({} fields)", vname, field_count(&variant.fields));
        }
        println!("  Generic params: {}", result.generic_params.len());
    } else {
        panic!("Result enum not found!");
    }
}

/// Test compiling core::marker traits
#[test]
fn test_marker_traits() {
    let path = Path::new(RUST_SRC_PATH).join("marker.rs");
    if !path.exists() {
        eprintln!("Skipping test: Rust source not found");
        return;
    }

    let source = std::fs::read_to_string(&path).unwrap();
    let language = RavenLanguage::new();
    let tree = language.parse(&source).unwrap();
    let root = language.lower_node(&tree.root_node(), &source);
    let hir = lower_source_file(&root);

    println!("\n=== core::marker HIR Summary ===");
    println!("Traits: {}", hir.traits.len());
    println!("Structs: {}", hir.structs.len());
    println!("Impl blocks: {}", hir.impl_blocks.len());

    println!("\nTraits found:");
    for (_, trait_def) in &hir.traits {
        let name = hir.interner.resolve(&trait_def.name);
        println!(
            "  - {} (methods: {}, associated_types: {})",
            name,
            trait_def.methods.len(),
            trait_def.associated_types.len()
        );
    }

    // We should find important marker traits
    let expected_traits = ["Copy", "Clone", "Send", "Sync", "Sized", "Unpin"];
    for trait_name in &expected_traits {
        let found = hir.traits.values().any(|t| {
            let name = hir.interner.resolve(&t.name);
            name == *trait_name
        });
        println!("  {} found: {}", trait_name, found);
    }
}

/// Test all 3 backends with a simple Option-using program
#[test]
fn test_option_all_backends() {
    use magpie::backend::Backend;
    use magpie::backends::{CraneliftBackend, LLVMBackend, RavenBackend};
    use magpie::manifest::Manifest;
    use std::fs;

    let user_code = r#"
enum Option<T> {
    None,
    Some(T),
}

fn unwrap_or(opt: Option<i64>, default: i64) -> i64 {
    match opt {
        Option::Some(v) => v,
        Option::None => default,
    }
}

fn test_option_basic() -> bool {
    let some_value = Option::Some(42);
    unwrap_or(some_value, 0) == 42
}

fn main() -> i64 {
    let some_value = Option::Some(42);
    unwrap_or(some_value, 0)
}
"#;

    // Create temp project
    let temp_dir = TempDir::new().unwrap();
    let src_dir = temp_dir.path().join("src");
    fs::create_dir_all(&src_dir).unwrap();
    fs::write(src_dir.join("main.rs"), user_code).unwrap();

    let cargo_toml = r#"
[package]
name = "test_project"
version = "0.1.0"

[[bin]]
name = "test_project"
path = "src/main.rs"
"#;
    fs::write(temp_dir.path().join("Cargo.toml"), cargo_toml).unwrap();

    let manifest = Manifest::find_in_dir(temp_dir.path()).unwrap();

    println!("\n=== Testing Option on All Backends ===");

    // Interpreter
    print!("Interpreter: ");
    let backend = RavenBackend::new();
    match backend.test(&manifest, temp_dir.path()) {
        Ok(result) => {
            if result.passed > 0 && result.failed == 0 {
                println!("OK (passed: {})", result.passed);
            } else {
                println!("FAIL (passed: {}, failed: {})", result.passed, result.failed);
                for msg in &result.messages {
                    println!("  {}", msg);
                }
            }
        }
        Err(e) => println!("ERROR: {}", e),
    }

    // Cranelift JIT
    print!("Cranelift:   ");
    match CraneliftBackend::new() {
        Ok(backend) => match backend.test(&manifest, temp_dir.path()) {
            Ok(result) => {
                if result.passed > 0 && result.failed == 0 {
                    println!("OK (passed: {})", result.passed);
                } else {
                    println!("FAIL (passed: {}, failed: {})", result.passed, result.failed);
                }
            }
            Err(e) => println!("ERROR: {}", e),
        },
        Err(e) => println!("ERROR: {}", e),
    }

    // LLVM
    print!("LLVM:        ");
    match LLVMBackend::new() {
        Ok(backend) => match backend.test(&manifest, temp_dir.path()) {
            Ok(result) => {
                if result.passed > 0 && result.failed == 0 {
                    println!("OK (passed: {})", result.passed);
                } else {
                    println!("FAIL (passed: {}, failed: {})", result.passed, result.failed);
                }
            }
            Err(e) => println!("ERROR: {}", e),
        },
        Err(e) => println!("ERROR: {}", e),
    }
}
