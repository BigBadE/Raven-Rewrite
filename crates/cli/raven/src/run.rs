//! Run command implementation

use anyhow::Result;
use colored::Colorize;
use std::path::Path;

pub fn run(path: &Path, backend: &str, _release: bool) -> Result<()> {
    println!("{} project at {:?}", "Running".green().bold(), path);

    // Find main entry point
    let main_file = find_main_file(path)?;

    // Compile the file
    println!("{} {:?}", "Compiling".bold(), main_file);
    let result = crate::compiler::compile_file(&main_file)?;

    // Find main function
    let _main_func = crate::compiler::find_main_function(&result.hir_ctx)
        .ok_or_else(|| anyhow::anyhow!("No main function found"))?;

    println!("  {} Parsed and lowered to HIR", "✓".green());
    println!("  {} Found main function", "✓".green());

    println!("\n{} main() with {} backend", "Executing".cyan().bold(), backend);
    println!("{}", "---".cyan());

    // TODO: Full execution pipeline
    // For now, demonstrate compilation success
    println!("  {} Compilation successful", "Success:".green());
    println!("  {} Execution not yet implemented for this CLI", "Note:".yellow());
    println!("  {} Use the integration tests for full execution", "Tip:".cyan());

    println!("{}", "---".cyan());
    println!("{} Compilation completed successfully", "Finished".green().bold());

    Ok(())
}

fn find_main_file(path: &Path) -> Result<std::path::PathBuf> {
    if path.is_file() {
        return Ok(path.to_path_buf());
    }

    let main_rs = path.join("src").join("main.rs");
    if main_rs.exists() {
        return Ok(main_rs);
    }

    anyhow::bail!("Could not find main.rs in {:?}", path);
}
