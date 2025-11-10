use rv_hir_lower::LoweringContext;
use rv_parser::parse_file;
use lang_raven::RavenLanguage;
use rv_vfs::{Vfs, FileId};
use rv_mir::lower_to_mir;
use rv_ty::infer_types;
use rv_llvm_backend::{compile_to_llvm_ir, OptLevel};

fn main() {
    let vfs = Vfs::new();
    let file_id = vfs.register_file("src/main.rs".into());
    
    let source = std::fs::read_to_string("src/main.rs").unwrap();
    let lang = RavenLanguage;
    let parse_result = parse_file(&source, &lang);
    
    let mut ctx = LoweringContext::new(file_id);
    ctx.lower_source_file(&parse_result.tree);
    
    let functions = ctx.functions().values().cloned().collect::<Vec<_>>();
    let structs = ctx.structs().values().cloned().collect::<Vec<_>>();
    let traits = ctx.traits().values().cloned().collect::<Vec<_>>();
    let impl_blocks = ctx.impl_blocks().clone();
    
    infer_types(&functions, &structs, &traits, &impl_blocks).unwrap();
    
    let mir_functions = functions.iter()
        .map(|f| lower_to_mir(f, &impl_blocks, &functions, &structs, &traits))
        .collect::<Result<Vec<_>, _>>().unwrap();
    
    let ir = compile_to_llvm_ir(&mir_functions, OptLevel::None).unwrap();
    println!("{}", ir);
}
