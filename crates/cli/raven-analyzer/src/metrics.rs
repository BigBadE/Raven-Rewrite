//! Metrics command implementation

use anyhow::Result;
use colored::Colorize;
use std::path::Path;

pub fn calculate_metrics(path: &Path, format: &str) -> Result<()> {
    if format == "text" {
        println!("{} metrics for {:?}", "Calculating".green().bold(), path);
    }

    // Find source files
    let source_files = find_source_files(path)?;

    if source_files.is_empty() {
        anyhow::bail!("No source files found in {:?}", path);
    }

    println!("  {} {} source files", "Found:".bold(), source_files.len());

    let mut all_metrics = Vec::new();

    // Analyze all files
    for file_path in &source_files {
        match crate::compiler::compile_to_hir(file_path) {
            Ok(hir_ctx) => {
                // Calculate metrics for each function
                for (_func_id, function) in &hir_ctx.functions {
                    let metrics = rv_metrics::analyze_function(function);
                    all_metrics.push(metrics);
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
            let json = serde_json::to_string_pretty(&all_metrics)?;
            println!("{}", json);
        }
        "text" => {
            if all_metrics.is_empty() {
                println!("\n{} No functions found", "Info:".cyan().bold());
            } else {
                println!("\n{} Metrics for {} functions:\n", "Results:".green().bold(), all_metrics.len());

                // Table header
                println!(
                    "{:<30} {:>10} {:>10} {:>10} {:>10}",
                    "Function", "Cyclomatic", "Cognitive", "Parameters", "Max Depth"
                );
                println!("{}", "-".repeat(80));

                // Calculate totals
                let mut total_cyclomatic = 0;
                let mut total_cognitive = 0;
                let mut total_params = 0;
                let mut max_depth_overall = 0;

                for metrics in &all_metrics {
                    println!(
                        "{:<30} {:>10} {:>10} {:>10} {:>10}",
                        truncate_name(&metrics.name, 30),
                        metrics.cyclomatic_complexity,
                        metrics.cognitive_complexity,
                        metrics.parameter_count,
                        metrics.max_nesting_depth
                    );

                    total_cyclomatic += metrics.cyclomatic_complexity;
                    total_cognitive += metrics.cognitive_complexity;
                    total_params += metrics.parameter_count;
                    max_depth_overall = max_depth_overall.max(metrics.max_nesting_depth);
                }

                println!("{}", "-".repeat(80));

                // Averages
                let count = all_metrics.len();
                println!(
                    "{:<30} {:>10.1} {:>10.1} {:>10.1} {:>10}",
                    "Average",
                    total_cyclomatic as f64 / count as f64,
                    total_cognitive as f64 / count as f64,
                    total_params as f64 / count as f64,
                    max_depth_overall
                );

                println!("\n{}", "Summary:".bold());
                println!("  Total functions: {}", count);
                println!("  Average cyclomatic complexity: {:.1}", total_cyclomatic as f64 / count as f64);
                println!("  Average cognitive complexity: {:.1}", total_cognitive as f64 / count as f64);
                println!("  Maximum nesting depth: {}", max_depth_overall);
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

fn truncate_name(name: &str, max_len: usize) -> String {
    if name.len() <= max_len {
        name.to_string()
    } else {
        format!("{}...", &name[..max_len - 3])
    }
}
