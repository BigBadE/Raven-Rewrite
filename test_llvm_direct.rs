// Direct test of LLVM backend compilation
use lang_raven::RavenLanguage;
use rv_hir_lower::lower_source_file;
use rv_mir::lower::LoweringContext;
use rv_syntax::Language;
use rv_ty::TypeInference;
use rv_llvm_backend::{compile_to_native, OptLevel};
use std::path::Path;

fn main() -> anyhow::Result<()> {
    let source = r#"
fn main() -> i64 {
    if true {
        100
    } else {
        200
    }
}
"#;

    println!("Parsing source...");
    let language = RavenLanguage::new();
    let tree = language.parse(source)?;
    let root = language.lower_node(&tree.root_node(), source);
    let hir = lower_source_file(&root);

    println!("Lowering to MIR...");
    let mut type_inference = TypeInference::new();
    for (_, func) in &hir.functions {
        type_inference.infer_function(func);
    }

    let mir_functions: Vec<_> = hir
        .functions
        .iter()
        .map(|(_, func)| {
            LoweringContext::lower_function(
                func,
                type_inference.context(),
                &hir.structs,
                &hir.impl_blocks,
                &hir.functions,
                &hir.types,
                &hir.traits,
            )
        })
        .collect();

    println!("Compiling to LLVM...");
    let output_path = Path::new("test_output.exe");
    compile_to_native(&mir_functions, output_path, OptLevel::Default)?;

    println!("Compilation successful!");
    println!("Trying to execute...");

    let status = std::process::Command::new(output_path).status()?;
    println!("Exit code: {:?}", status.code());

    Ok(())
}
