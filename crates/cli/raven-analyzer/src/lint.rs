//! Lint command implementation

use anyhow::Result;
use colored::Colorize;
use rv_lint::{ComplexityRule, CognitiveComplexityRule, DeepNestingRule, LintLevel, Linter, TooManyParametersRule, UnusedVariableRule};
use std::path::Path;

pub fn run_lint(
    path: &Path,
    format: &str,
    max_complexity: usize,
    max_parameters: usize,
) -> Result<()> {
    if format == "text" {
        println!("{} code in {:?}", "Linting".green().bold(), path);
    }

    // Find source files
    let source_files = find_source_files(path)?;

    if source_files.is_empty() {
        anyhow::bail!("No source files found in {:?}", path);
    }

    println!("  {} {} source files", "Found:".bold(), source_files.len());
    println!("  {} max_complexity={}, max_parameters={}", "Config:".bold(), max_complexity, max_parameters);

    // Create linter with custom thresholds
    let linter = Linter::with_rules(vec![
        Box::new(ComplexityRule { max_complexity }),
        Box::new(TooManyParametersRule { max_parameters }),
        Box::new(DeepNestingRule::default()),
        Box::new(CognitiveComplexityRule::default()),
        Box::new(UnusedVariableRule),
    ]);

    let mut all_diagnostics = Vec::new();

    // Lint all files
    for file_path in &source_files {
        match crate::compiler::compile_to_hir(file_path) {
            Ok(hir_ctx) => {
                // Lint each function
                for (_func_id, function) in &hir_ctx.functions {
                    let diagnostics = linter.lint_function(function);
                    all_diagnostics.extend(diagnostics);
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
            let json = serde_json::to_string_pretty(&all_diagnostics)?;
            println!("{}", json);
        }
        "text" => {
            if all_diagnostics.is_empty() {
                println!("\n{} No issues found", "Success:".green().bold());
            } else {
                println!("\n{} {} issues found:\n", "Found".yellow().bold(), all_diagnostics.len());

                for diagnostic in &all_diagnostics {
                    let level_str = match diagnostic.level {
                        LintLevel::Error => "error".red().bold(),
                        LintLevel::Warning => "warning".yellow().bold(),
                        LintLevel::Info => "info".cyan().bold(),
                    };

                    println!("{}: {} [{}]", level_str, diagnostic.message, diagnostic.rule);
                    println!("  --> {:?}", diagnostic.span);

                    if let Some(suggestion) = &diagnostic.suggestion {
                        println!("  {} {}", "help:".cyan().bold(), suggestion);
                    }
                    println!();
                }

                // Summary
                let errors = all_diagnostics.iter().filter(|d| d.level == LintLevel::Error).count();
                let warnings = all_diagnostics.iter().filter(|d| d.level == LintLevel::Warning).count();

                if errors > 0 {
                    println!("{} {} errors, {} warnings", "Summary:".bold(), errors, warnings);
                } else {
                    println!("{} {} warnings", "Summary:".bold(), warnings);
                }
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
