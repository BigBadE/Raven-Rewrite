use hir::resolve_to_hir;
use mir::{MediumSyntaxLevel, resolve_to_mir};
use parser::parse_source;
use std::path::PathBuf;
use syntax::Syntax;
use syntax::util::CompileError;

/// Compiles a directory into a Syntax
pub async fn compile_source(dir: PathBuf) -> Result<Syntax<MediumSyntaxLevel>, CompileError> {
    let raw_source = parse_source(dir).await?;

    let hir = resolve_to_hir(raw_source)?;
    let mir = resolve_to_mir(hir)?;

    Ok(mir)
}
