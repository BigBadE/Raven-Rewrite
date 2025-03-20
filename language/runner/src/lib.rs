use parser::parse_source;
use std::path::PathBuf;
use syntax::hir::resolve_to_hir;
use syntax::mir::{resolve_to_mir, MediumSyntaxLevel};
use syntax::util::ParseError;
use syntax::Syntax;

pub async fn compile_source(dir: PathBuf) -> Result<Syntax<MediumSyntaxLevel>, ParseError> {
    let raw_source = parse_source(dir).await?;

    let hir = resolve_to_hir(raw_source)?;
    let mir = resolve_to_mir(hir)?;

    Ok(mir)
}
