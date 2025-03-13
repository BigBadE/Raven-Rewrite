use parser::parse_source;
use std::path::PathBuf;

use syntax::hir::{resolve_to_hir, HighSyntaxLevel};
use syntax::Syntax;
use syntax::util::ParseError;

pub async fn compile_source(dir: PathBuf) -> Result<Syntax<HighSyntaxLevel>, ParseError> {
    let raw_source = parse_source(dir).await?;

    let hir = resolve_to_hir(raw_source)?;
    // Need type resolution
    // Need a MIL (CFG)
    // Need a SSA
    // Need LLVMIR

    Ok(hir)
}