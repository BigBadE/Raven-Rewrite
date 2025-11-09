//! Duplicates detection command implementation

use anyhow::Result;
use colored::Colorize;
use rv_duplicates::DuplicateDetector;
use std::path::Path;

pub fn detect_duplicates(
    path: &Path,
    format: &str,
    min_similarity: u8,
    min_expressions: usize,
) -> Result<()> {
    if format == "text" {
        println!("{} duplicate code in {:?}", "Detecting".green().bold(), path);
    }

    // Find source files
    let source_files = find_source_files(path)?;

    if source_files.is_empty() {
        anyhow::bail!("No source files found in {:?}", path);
    }

    println!("  {} {} source files", "Found:".bold(), source_files.len());
    println!("  {} min_similarity={}%, min_expressions={}", "Config:".bold(), min_similarity, min_expressions);

    // Create detector with custom thresholds
    let detector = DuplicateDetector::new()
        .with_min_similarity(min_similarity)
        .with_min_expressions(min_expressions);

    let mut all_duplicates = Vec::new();

    // Analyze all files
    for file_path in &source_files {
        match crate::compiler::compile_to_hir(file_path) {
            Ok(hir_ctx) => {
                // Detect duplicates within each function
                for (_func_id, function) in &hir_ctx.functions {
                    let duplicates = detector.detect_in_function(function);
                    all_duplicates.extend(duplicates);
                }

                // Detect duplicates across functions in this file
                let functions: Vec<_> = hir_ctx.functions.values().collect();
                if functions.len() > 1 {
                    let cross_duplicates = detector.detect_across_functions(&functions);
                    all_duplicates.extend(cross_duplicates);
                }
            }
            Err(e) => {
                if format == "text" {
                    eprintln!("{} Failed to parse {:?}: {}", "Warning:".yellow().bold(), file_path, e);
                }
            }
        }
    }

    // Output results
    match format {
        "json" => {
            let json = serde_json::to_string_pretty(&all_duplicates)?;
            println!("{}", json);
        }
        "text" => {
            if all_duplicates.is_empty() {
                println!("\n{} No duplicates found", "Success:".green().bold());
            } else {
                println!(
                    "\n{} {} duplicate code blocks found:\n",
                    "Found".yellow().bold(),
                    all_duplicates.len()
                );

                for (i, duplicate) in all_duplicates.iter().enumerate() {
                    println!("{}. Duplicate code ({}% similar)", i + 1, duplicate.similarity);
                    println!("   First occurrence:  {:?}", duplicate.first);
                    println!("   Second occurrence: {:?}", duplicate.second);
                    println!("   Expression count: {}", duplicate.expression_count);
                    println!();
                }

                // Summary
                let avg_similarity = all_duplicates.iter()
                    .map(|d| d.similarity as usize)
                    .sum::<usize>() / all_duplicates.len();

                println!("{}", "Summary:".bold());
                println!("  Total duplicates: {}", all_duplicates.len());
                println!("  Average similarity: {}%", avg_similarity);
                println!("  Threshold: {}%", min_similarity);
            }
        }
        _ => anyhow::bail!("Unknown format: {}", format),
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
