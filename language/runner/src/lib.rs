use std::collections::HashMap;
use hir::{resolve_to_hir, HighSyntaxLevel};
use mir::{MediumSyntaxLevel, resolve_to_mir};
use parser::{parse_source, parse_source_with_tests};
use std::path::PathBuf;
use syntax::{GenericFunctionRef, Syntax};
use syntax::util::CompileError;
use std::sync::Arc;
use lasso::ThreadedRodeo;
use hir::function::HighFunction;

/// Compiles a directory into both HIR and MIR
/// Returns a tuple of (HIR functions with attributes, symbols, MIR syntax for compilation)
pub async fn compile_source_with_hir(dir: PathBuf) -> Result<(HashMap<GenericFunctionRef, HighFunction<HighSyntaxLevel>>,
                                                              Arc<ThreadedRodeo>, Syntax<MediumSyntaxLevel>), CompileError> {
    let raw_source = parse_source(dir).await?;

    let hir = resolve_to_hir(raw_source)?;
    println!("=== HIR ===");
    println!("{}", hir.syntax);

    // Extract HIR functions and symbols before consuming HIR
    let hir_functions = hir.syntax.functions.clone();
    let hir_symbols = hir.syntax.symbols.clone();

    let mir = resolve_to_mir(hir)?;

    Ok((hir_functions, hir_symbols, mir))
}

/// Compiles a directory including tests into both HIR and MIR
/// Returns a tuple of (HIR functions with attributes, symbols, MIR syntax for compilation)
pub async fn compile_source_with_tests_and_hir(dir: PathBuf) -> Result<(HashMap<GenericFunctionRef, HighFunction<HighSyntaxLevel>>,
                                                                        Arc<ThreadedRodeo>, Syntax<MediumSyntaxLevel>), CompileError> {
    let raw_source = parse_source_with_tests(dir).await?;

    let hir = resolve_to_hir(raw_source)?;
    println!("=== HIR ===");
    println!("{}", hir.syntax);

    // Extract HIR functions and symbols before consuming HIR
    let hir_functions = hir.syntax.functions.clone();
    let hir_symbols = hir.syntax.symbols.clone();

    let mir = resolve_to_mir(hir)?;

    Ok((hir_functions, hir_symbols, mir))
}
