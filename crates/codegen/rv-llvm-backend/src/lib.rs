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
use rv_hir::FunctionId;
use rv_lir::{LirExternalFunction, LirFunction};
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
    external_functions: &HashMap<FunctionId, LirExternalFunction>,
    output_path: &Path,
    opt_level: OptLevel,
) -> Result<()> {
    // Use a unique module name to avoid conflicts
    let module_name = format!(
        "raven_module_{}",
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock is before UNIX epoch")
            .as_nanos()
    );
    let backend = LLVMBackend::new(&module_name, opt_level)?;

    // Write object file directly (combined compile + write for efficiency)
    let obj_path = output_path.with_extension("o");
    backend.compile_and_write_object(functions, external_functions, &obj_path)?;

    // Debug: Write LLVM IR to file
    if std::env::var("DEBUG_LLVM_IR").is_ok() {
        let ir_path = output_path.with_extension("ll");
        std::fs::write(&ir_path, backend.to_llvm_ir())?;
    }

    // Link object file to executable using main() entry point
    link_object_to_executable(&obj_path, output_path)?;

    // Clean up object file
    let _ = std::fs::remove_file(&obj_path);

    Ok(())
}

/// Detect the system linker once by checking what is available on the PATH.
/// Returns the linker command name on success.
fn detect_linker() -> Result<&'static str> {
    use std::process::Command;

    if cfg!(target_family = "unix") {
        // On Unix/Linux, GCC is the standard system linker driver
        if Command::new("gcc").arg("--version").output().is_ok() {
            return Ok("gcc");
        }
        anyhow::bail!(
            "No linker found. GCC is required for linking on Unix/Linux.\n\
             Install it with: apt install gcc (Debian/Ubuntu) or dnf install gcc (Fedora)"
        );
    } else if cfg!(target_family = "windows") {
        // On Windows, use LLVM's MSVC-compatible linker
        if Command::new("lld-link").arg("--version").output().is_ok() {
            return Ok("lld-link");
        }
        anyhow::bail!(
            "No linker found. lld-link is required for linking on Windows.\n\
             Install LLVM or use the Visual Studio Build Tools."
        );
    } else {
        anyhow::bail!("Unsupported platform for native linking");
    }
}

fn link_object_to_executable(obj_path: &Path, output_path: &Path) -> Result<()> {
    use std::process::Command;

    let linker = detect_linker()?;

    let output = match linker {
        "gcc" => Command::new("gcc")
            .arg("-o")
            .arg(output_path)
            .arg(obj_path)
            .output()
            .map_err(|e| anyhow::anyhow!("Failed to execute gcc: {}", e))?,
        "lld-link" => Command::new("lld-link")
            .arg(format!("/OUT:{}", output_path.display()))
            .arg(obj_path)
            .arg("/SUBSYSTEM:CONSOLE")
            .arg("/ENTRY:main")
            .output()
            .map_err(|e| anyhow::anyhow!("Failed to execute lld-link: {}", e))?,
        other => anyhow::bail!("Unknown linker: {}", other),
    };

    if output.status.success() {
        Ok(())
    } else {
        anyhow::bail!(
            "{} linking failed:\n  stdout: {}\n  stderr: {}",
            linker,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
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
