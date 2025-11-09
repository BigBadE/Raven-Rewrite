//! Check command implementation

use anyhow::Result;
use colored::Colorize;
use std::path::Path;

pub fn check(path: &Path) -> Result<()> {
    println!("{} project at {:?}", "Checking".green().bold(), path);

    // Find source files
    let source_files = find_source_files(path)?;

    if source_files.is_empty() {
        anyhow::bail!("No source files found in {:?}", path);
    }

    println!("  {} {} source files", "Found:".bold(), source_files.len());

    let mut total_errors = 0;
    let total_warnings = 0;

    // Check all files
    for file_path in &source_files {
        println!("\n  {} {:?}", "Checking:".bold(), file_path);

        match crate::compiler::compile_file(file_path) {
            Ok(result) => {
                println!("    {} Parsed successfully", "✓".green());
                println!("    {} {} functions in HIR", "✓".green(), result.hir_ctx.functions.len());
                println!("    {} Name resolution complete", "✓".green());
            }
            Err(e) => {
                total_errors += 1;
                eprintln!("    {} {}", "✗".red(), e);
            }
        }
    }

    println!();
    if total_errors == 0 && total_warnings == 0 {
        println!("{} No errors found", "Success:".green().bold());
    } else {
        if total_errors > 0 {
            eprintln!("{} {} errors found", "Failed:".red().bold(), total_errors);
        }
        if total_warnings > 0 {
            eprintln!("{} {} warnings found", "Warning:".yellow().bold(), total_warnings);
        }

        if total_errors > 0 {
            anyhow::bail!("Check failed with {} errors", total_errors);
        }
    }

    Ok(())
}

fn find_source_files(path: &Path) -> Result<Vec<std::path::PathBuf>> {
    let mut files = Vec::new();

    if path.is_file() {
        if path.extension().map_or(false, |ext| ext == "rs") {
            files.push(path.to_path_buf());
        }
    } else if path.is_dir() {
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

    Ok(files)
}
