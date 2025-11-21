use rv_hir_lower::LoweringContext;
use rv_parser::parse_file;
use rv_intern::Interner;
use lang_raven::RavenLanguage;
use std::fs;

fn main() {
    let source = fs::read_to_string("crates/testing/integration-tests/test-projects/14-traits/src/main.rs").unwrap();
    
    let mut interner = Interner::new();
    let lang = RavenLanguage;
    let parse_result = parse_file(&lang, &source);
    
    let mut ctx = LoweringContext::new(&mut interner);
    let hir = ctx.lower_file(&parse_result.tree);
    
    // Find the process function
    for (func_id, func) in &hir.functions {
        if interner.resolve(&func.name) == "process" {
            println!("Found process function: {:?}", func_id);
            println!("Parameters: {:?}", func.parameters);
            println!("Body root expr: {:?}", func.body.root_expr);
            println!("All exprs: {:#?}", func.body.exprs);
        }
    }
}
