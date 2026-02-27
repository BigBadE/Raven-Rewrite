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

    // Find main entry point
    let main_file = find_main_file(path)?;

    println!("  {} {:?}", "Compiling:".bold(), main_file);

    // Compile through HIR
    let result = crate::compiler::compile_file(&main_file)?;

    let func_count = result.hir_ctx.functions.len();
    println!(
        "    {} Parsed and lowered {} functions to HIR",
        "\u{2713}".green(),
        func_count
    );

    // Verify main function exists
    crate::compiler::find_main_function(&result.hir_ctx)
        .ok_or_else(|| anyhow::anyhow!("No main function found"))?;

    // Run coherence checking
    crate::compiler::check_coherence(&result.hir_ctx)?;

    // Lower to MIR with type inference
    let (_inference_result, mut mir_functions) = crate::compiler::lower_to_mir(&result.hir_ctx)?;

    println!(
        "    {} Lowered {} functions to MIR",
        "\u{2713}".green(),
        mir_functions.len()
    );

    // Monomorphize generic functions
    crate::compiler::monomorphize(&result.hir_ctx, &mut mir_functions);

    // Determine output directory
    let output_dir = if path.is_file() {
        path.parent().unwrap_or(Path::new(".")).join("target")
    } else {
        path.join("target")
    };
    std::fs::create_dir_all(&output_dir)?;

    // Generate output based on backend
    match backend {
        "llvm" => {
            let opt_level = if release {
                rv_llvm_backend::OptLevel::Aggressive
            } else {
                rv_llvm_backend::OptLevel::None
            };

            // Lower MIR to LIR
            let lir_functions = rv_lir::lower::lower_mir_to_lir(mir_functions, &result.hir_ctx);
            let lir_externals = rv_lir::lower::lower_external_functions(
                &result.hir_ctx.external_functions,
                &result.hir_ctx.types,
                &result.hir_ctx.interner,
            );

            let exe_name = if cfg!(windows) {
                "output.exe".to_string()
            } else {
                "output".to_string()
            };
            let exe_path = output_dir.join(&exe_name);

            rv_llvm_backend::compile_to_native_with_externals(
                &lir_functions,
                &lir_externals,
                &exe_path,
                opt_level,
            )?;

            println!(
                "    {} LLVM: Compiled to {}",
                "\u{2713}".green(),
                exe_path.display()
            );
        }
        "cranelift" | "jit" => {
            // Cranelift is a JIT backend - verify compilation succeeds
            let mut jit = rv_cranelift::JitCompiler::new()?;

            if !mir_functions.is_empty() {
                jit.compile_multiple(&mir_functions)?;
            }

            println!(
                "    {} Cranelift: JIT compilation verified",
                "\u{2713}".green()
            );
        }
        "interpreter" => {
            // Interpreter doesn't produce output artifacts, just verify the pipeline
            println!(
                "    {} Interpreter: Pipeline verified (no native output)",
                "\u{2713}".green()
            );
        }
        _ => {
            anyhow::bail!(
                "Unknown backend '{}'. Use 'interpreter', 'cranelift', or 'llvm'",
                backend
            );
        }
    }

    let duration = start.elapsed();
    println!(
        "\n{} Compiled in {:.2}s",
        "Finished".green().bold(),
        duration.as_secs_f64()
    );

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

    anyhow::bail!("Could not find main.rs in {:?}", path)
}
