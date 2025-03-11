use parser::parse_source;
use std::path::PathBuf;
use syntax::LowSyntax;

pub use parser::ParseError;
use syntax::hir::resolve_to_hir;

pub async fn compile_source(dir: PathBuf) -> Result<LowSyntax, ParseError> {
    let raw_source = parse_source(dir).await?;

    let hir = resolve_to_hir(raw_source);
    // Need type resolution
    // Need a MIL (CFG)
    // Need a SSA
    // Need LLVMIR

    Ok(hir)
}