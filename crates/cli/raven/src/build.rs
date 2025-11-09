//! Build command implementation

use anyhow::Result;
use colored::Colorize;
use std::path::Path;
use std::time::Instant;

pub fn build(path: &Path, backend: &str, release: bool) -> Result<()> {
    let start = Instant::now();

    println!("{} project at {:?}", "Compiling".green().bold(), path);

    if release {
        println!("  {} Release mode with optimizations", "Mode:".bold());
    }
    println!("  {} {}", "Backend:".bold(), backend);

    // Find source files
    let source_files = find_source_files(path)?;

    if source_files.is_empty() {
        anyhow::bail!("No source files found in {:?}", path);
    }

    println!("  {} {} source files", "Found:".bold(), source_files.len());

    // Compile all files
    for file_path in &source_files {
        println!("\n  {} {:?}", "Compiling:".bold(), file_path);

        let result = crate::compiler::compile_file(file_path)?;

        println!("    {} Parsed successfully", "✓".green());
        println!("    {} {} functions lowered to HIR", "✓".green(), result.hir_ctx.functions.len());
        println!("    {} Name resolution complete", "✓".green());
    }

    println!("\n  {} Backend: {}", "Target:".bold(), backend);

    // Generate output based on backend
    match backend {
        "llvm" => {
            println!("    {} LLVM backend selected (output to object file)", "Info:".bold());
            // TODO: When MIR is ready, generate object file
        }
        "cranelift" => {
            println!("    {} Cranelift JIT compilation", "Info:".bold());
        }
        "interpreter" => {
            println!("    {} Interpreter mode (no native code)", "Info:".bold());
        }
        _ => {
            println!("    {} Defaulting to interpreter", "Info:".bold());
        }
    }

    let duration = start.elapsed();
    println!(
        "\n  {} Compiled in {:.2}s",
        "Finished".green().bold(),
        duration.as_secs_f64()
    );

    Ok(())
}

fn find_source_files(path: &Path) -> Result<Vec<std::path::PathBuf>> {
    let mut files = Vec::new();

    if path.is_file() {
        if path.extension().map_or(false, |ext| ext == "rs") {
            files.push(path.to_path_buf());
        }
    } else if path.is_dir() {
        // Look for src/main.rs or src/lib.rs
        let main_rs = path.join("src").join("main.rs");
        let lib_rs = path.join("src").join("lib.rs");

        if main_rs.exists() {
            files.push(main_rs);
        } else if lib_rs.exists() {
            files.push(lib_rs);
        } else {
            // Collect all .rs files in src/
            let src_dir = path.join("src");
            if src_dir.exists() {
                for entry in std::fs::read_dir(src_dir)? {
                    let entry = entry?;
                    let file_path = entry.path();
                    if file_path.extension().map_or(false, |ext| ext == "rs") {
                        files.push(file_path);
                    }
                }
            }
        }
    }

    Ok(files)
}
