#![allow(missing_docs)]
// Standalone tests to parse core library files through our pipeline
// Run with: cargo test -p rv-hir-lower --test test_core_parse

use std::path::PathBuf;

fn get_core_src_path(relative: &str) -> Option<PathBuf> {
    let home = std::env::var("HOME").ok()?;
    let path = PathBuf::from(format!(
        "{}/.rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/{}",
        home, relative
    ));
    if path.exists() {
        Some(path)
    } else {
        None
    }
}

fn parse_and_report(label: &str, path: &PathBuf) -> rv_hir_lower::LoweringContext {
    let source = std::fs::read_to_string(path).unwrap();
    let parse_result = rv_parser::parse_source(&source);

    let root = parse_result.syntax.as_ref().expect("should parse");
    println!("Parse errors: {}", parse_result.errors.len());

    let ctx = rv_hir_lower::lower_source_file(root);

    println!("\n=== Lowering Results for {} ===", label);
    println!("Functions: {}", ctx.functions.len());
    println!("Structs: {}", ctx.structs.len());
    println!("Enums: {}", ctx.enums.len());
    println!("Traits: {}", ctx.traits.len());
    println!("Impl blocks: {}", ctx.impl_blocks.len());
    println!("Const items: {}", ctx.const_items.len());
    println!("Static items: {}", ctx.static_items.len());
    println!("Type aliases: {}", ctx.type_aliases.len());

    println!("\n=== Diagnostics ({}) ===", ctx.diagnostics.len());
    let mut counts: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
    for d in &ctx.diagnostics {
        *counts.entry(d.message.clone()).or_insert(0) += 1;
    }
    let mut sorted: Vec<_> = counts.into_iter().collect();
    sorted.sort_by(|a, b| b.1.cmp(&a.1));
    for (msg, count) in &sorted {
        println!("  [{:>3}x] {}", count, msg);
    }

    ctx
}

#[test]
fn parse_core_marker() {
    let path = match get_core_src_path("marker.rs") {
        Some(p) => p,
        None => {
            println!("Skipping: core/src/marker.rs not found");
            return;
        }
    };

    let ctx = parse_and_report("core/src/marker.rs", &path);

    assert!(!ctx.traits.is_empty(), "Should find traits in marker.rs");
    println!("\nTraits found:");
    for (id, t) in &ctx.traits {
        let name = ctx.interner.resolve(&t.name);
        println!(
            "  {:?}: {} (attrs: {}, auto: {}, unsafe: {})",
            id,
            name,
            t.attributes.len(),
            t.is_auto,
            t.is_unsafe
        );
    }
}

#[test]
fn parse_core_num_mod() {
    let path = match get_core_src_path("num/mod.rs") {
        Some(p) => p,
        None => {
            println!("Skipping: core/src/num/mod.rs not found");
            return;
        }
    };

    let ctx = parse_and_report("core/src/num/mod.rs", &path);

    let total_items = ctx.functions.len()
        + ctx.structs.len()
        + ctx.enums.len()
        + ctx.traits.len()
        + ctx.impl_blocks.len()
        + ctx.const_items.len()
        + ctx.type_aliases.len();
    assert!(total_items > 0, "Should find items in num/mod.rs");

    println!("\nType aliases:");
    for (_id, ta) in &ctx.type_aliases {
        let name = ctx.interner.resolve(&ta.name);
        println!("  {}", name);
    }
    println!("\nEnums:");
    for (_id, e) in &ctx.enums {
        let name = ctx.interner.resolve(&e.name);
        println!("  {} ({} variants)", name, e.variants.len());
    }
}

#[test]
fn parse_core_option() {
    let path = match get_core_src_path("option.rs") {
        Some(p) => p,
        None => {
            println!("Skipping: core/src/option.rs not found");
            return;
        }
    };

    let ctx = parse_and_report("core/src/option.rs", &path);

    assert!(
        !ctx.enums.is_empty(),
        "Should find Option enum in option.rs"
    );
    println!("\nEnums:");
    for (_id, e) in &ctx.enums {
        let name = ctx.interner.resolve(&e.name);
        println!("  {} ({} variants)", name, e.variants.len());
    }
    println!("\nImpl blocks: {}", ctx.impl_blocks.len());
    println!("\nFunctions: {}", ctx.functions.len());
}
