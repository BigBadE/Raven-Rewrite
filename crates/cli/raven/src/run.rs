//! Run command implementation

use anyhow::{Context, Result};
use colored::Colorize;
use std::path::Path;

#[allow(unsafe_code)]
pub fn run(path: &Path, backend: &str, _release: bool) -> Result<()> {
    println!("{} project at {:?}", "Running".green().bold(), path);

    // Find main entry point
    let main_file = find_main_file(path)?;

    // Compile through HIR
    println!("{} {:?}", "Compiling".bold(), main_file);
    let result = crate::compiler::compile_file(&main_file)?;

    // Find main function
    let _main_func = crate::compiler::find_main_function(&result.hir_ctx)
        .ok_or_else(|| anyhow::anyhow!("No main function found"))?;

    println!("  {} Parsed and lowered to HIR", "\u{2713}".green());

    // Run coherence checking
    crate::compiler::check_coherence(&result.hir_ctx)?;

    // Lower to MIR with type inference
    let (inference_result, mut mir_functions) = crate::compiler::lower_to_mir(&result.hir_ctx)?;

    println!(
        "  {} Lowered {} functions to MIR",
        "\u{2713}".green(),
        mir_functions.len()
    );

    // Monomorphize generic functions
    crate::compiler::monomorphize(&result.hir_ctx, &mut mir_functions);

    // Find the main MIR function
    let main_mir = mir_functions
        .iter()
        .find(|f| {
            result
                .hir_ctx
                .functions
                .get(&f.id)
                .map_or(false, |hir_func| {
                    result.hir_ctx.interner.resolve(&hir_func.name) == "main"
                })
        })
        .context("main function not found in MIR")?;

    let main_id = main_mir.id;

    println!(
        "\n{} main() with {} backend",
        "Executing".cyan().bold(),
        backend
    );
    println!("{}", "---".cyan());

    let exit_code: i64 = match backend {
        "interpreter" => {
            let mut interpreter = rv_interpreter::Interpreter::new_with_context(
                &result.hir_ctx,
                &inference_result.ctx,
            );

            // Register all non-main functions so the interpreter can call them
            for mir_func in &mir_functions {
                if mir_func.id != main_id {
                    interpreter.register_mir_function(mir_func.id, mir_func.clone());
                }
            }

            let value = interpreter
                .execute(
                    mir_functions
                        .iter()
                        .find(|f| f.id == main_id)
                        .context("main not found")?,
                )
                .map_err(|e| anyhow::anyhow!("Interpreter error: {}", e))?;

            println!("{value}");
            match value.as_int() {
                Some(code) => code,
                None => {
                    eprintln!(
                        "warning: main() returned non-integer value '{}', using exit code 0",
                        value
                    );
                    0
                }
            }
        }
        "cranelift" | "jit" => {
            let mut jit = rv_cranelift::JitCompiler::new()?;
            jit.compile_multiple(&mir_functions)?;
            let code_ptr = jit
                .compiled_functions
                .get(&main_id)
                .copied()
                .context("main function was not compiled")?;
            unsafe { jit.execute(code_ptr) }
        }
        "llvm" => {
            // Lower MIR to LIR (takes ownership of mir_functions)
            let lir_functions = rv_lir::lower::lower_mir_to_lir(mir_functions, &result.hir_ctx);
            let lir_externals = rv_lir::lower::lower_external_functions(
                &result.hir_ctx.external_functions,
                &result.hir_ctx.types,
                &result.hir_ctx.interner,
            );

            // Compile to native executable
            let temp_dir = std::env::temp_dir().join("raven_build");
            std::fs::create_dir_all(&temp_dir)?;
            let exe_name = if cfg!(windows) {
                "output.exe".to_string()
            } else {
                "output".to_string()
            };
            let exe_path = temp_dir.join(&exe_name);

            rv_llvm_backend::compile_to_native_with_externals(
                &lir_functions,
                &lir_externals,
                &exe_path,
                rv_llvm_backend::OptLevel::None,
            )?;

            // Execute the compiled binary
            let status = std::process::Command::new(&exe_path)
                .status()
                .context("Failed to execute LLVM-compiled binary")?;

            status.code().unwrap_or(1).into()
        }
        _ => {
            anyhow::bail!(
                "Unknown backend '{}'. Use 'interpreter', 'cranelift', or 'llvm'",
                backend
            );
        }
    };

    println!("{}", "---".cyan());
    println!(
        "{} Process exited with code {}",
        "Finished".green().bold(),
        exit_code
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

    anyhow::bail!("Could not find main.rs in {:?}", path);
}
