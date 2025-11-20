//! LLVM backend for Raven
//!
//! This crate provides code generation using LLVM through the inkwell library.
//! It translates LIR (Low-level IR) into LLVM IR and performs optimization.
//!
//! LIR is fully monomorphized - the type system guarantees no generic functions reach this backend.
//!
//! LLVM is automatically downloaded during build.

mod codegen;
mod types;

pub use codegen::LLVMBackend;

use anyhow::Result;
use rv_hir::{ExternalFunction, FunctionId};
use rv_lir::LirFunction;
use std::collections::HashMap;
use std::path::Path;

/// Compile LIR to native code using LLVM
///
/// Type system guarantee: LirFunction cannot contain generic functions.
/// All monomorphization has already been performed.
pub fn compile_to_native(
    functions: &[LirFunction],
    output_path: &Path,
    opt_level: OptLevel,
) -> Result<()> {
    compile_to_native_with_externals(functions, &HashMap::new(), output_path, opt_level)
}

/// Compile LIR to native code with external function support
pub fn compile_to_native_with_externals(
    functions: &[LirFunction],
    external_functions: &HashMap<FunctionId, ExternalFunction>,
    output_path: &Path,
    opt_level: OptLevel,
) -> Result<()> {
    // Use a unique module name to avoid conflicts
    let module_name = format!("raven_module_{}", std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos());
    let backend = LLVMBackend::new(&module_name, opt_level)?;

    // Write object file directly (combined compile + write for efficiency)
    let obj_path = output_path.with_extension("o");
    backend.compile_and_write_object(functions, external_functions, &obj_path)?;

    // Debug: Write LLVM IR to file
    if std::env::var("DEBUG_LLVM_IR").is_ok() {
        let ir_path = output_path.with_extension("ll");
        std::fs::write(&ir_path, backend.to_llvm_ir())?;
    }

    // Link object file to executable
    // Use the first function as entry point (typically func_0 or main)
    let entry_point = if !functions.is_empty() {
        format!("func_{}", functions[0].id.0)
    } else {
        "func_0".to_string()
    };
    link_object_to_executable(&obj_path, output_path, &entry_point)?;

    // Clean up object file
    let _ = std::fs::remove_file(&obj_path);

    Ok(())
}

fn link_object_to_executable(obj_path: &Path, output_path: &Path, entry_point: &str) -> Result<()> {
    use std::process::Command;

    // Try linkers in order of preference:
    // 1. GCC (Unix, Linux, MINGW with GCC installed)
    // 2. ld.lld (LLVM's linker - cross-platform)
    // 3. lld-link (LLVM's MSVC-compatible linker)

    let mut errors = Vec::new();

    // Try GCC first
    if let Ok(output) = Command::new("gcc")
        .arg("-o")
        .arg(output_path)
        .arg(obj_path)
        .arg("-e")
        .arg(entry_point)
        .arg("-no-pie")
        .output()
    {
        if output.status.success() {
            return Ok(());
        } else {
            errors.push(format!(
                "gcc failed:\n  stdout: {}\n  stderr: {}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
    }

    // Try ld.lld (LLVM linker)
    if let Ok(output) = Command::new("ld.lld")
        .arg("-o")
        .arg(output_path)
        .arg(obj_path)
        .arg("-e")
        .arg(entry_point)
        .output()
    {
        if output.status.success() {
            return Ok(());
        } else {
            errors.push(format!(
                "ld.lld failed:\n  stdout: {}\n  stderr: {}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
    }

    // Try lld-link (LLVM's MSVC-compatible linker)
    if let Ok(output) = Command::new("lld-link")
        .arg(format!("/OUT:{}", output_path.display()))
        .arg(obj_path)
        .arg("/SUBSYSTEM:CONSOLE")
        .arg(format!("/ENTRY:{}", entry_point))
        .output()
    {
        if output.status.success() {
            return Ok(());
        } else {
            errors.push(format!(
                "lld-link failed:\n  stdout: {}\n  stderr: {}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
    }

    // All linkers failed or none found
    if errors.is_empty() {
        anyhow::bail!(
            "No linker found. Please ensure one of the following is in your PATH:\n\
             - gcc (for Unix/Linux/MINGW)\n\
             - ld.lld (LLVM linker)\n\
             - lld-link (LLVM MSVC-compatible linker)"
        );
    } else {
        anyhow::bail!(
            "All linkers failed:\n{}",
            errors.join("\n\n")
        );
    }
}

/// Compile LIR to LLVM IR (text representation)
pub fn compile_to_llvm_ir(functions: &[LirFunction], opt_level: OptLevel) -> Result<String> {
    let backend = LLVMBackend::new("raven_module", opt_level)?;

    backend.compile_functions(functions)?;

    Ok(backend.to_llvm_ir())
}

/// LLVM optimization levels
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptLevel {
    /// No optimization
    None,
    /// Less optimization
    Less,
    /// Default optimization
    Default,
    /// Aggressive optimization
    Aggressive,
}

impl OptLevel {
    pub fn to_inkwell(&self) -> inkwell::OptimizationLevel {
        match self {
            OptLevel::None => inkwell::OptimizationLevel::None,
            OptLevel::Less => inkwell::OptimizationLevel::Less,
            OptLevel::Default => inkwell::OptimizationLevel::Default,
            OptLevel::Aggressive => inkwell::OptimizationLevel::Aggressive,
        }
    }
}
