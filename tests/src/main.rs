use anyhow::Error;
use compiler_llvm::LowCompiler;
use lasso::ThreadedRodeo;
use runner::{compile_source_with_hir, compile_source_with_tests_and_hir};
use std::path::PathBuf;
use syntax::structure::Attribute;
use syntax::util::pretty_print::PrettyPrint;

type TestFunction = unsafe extern "C" fn() -> i32;

fn main() {}

/// Check if a function has the #[test] attribute or starts with "test_"
fn is_test_function(attributes: &[Attribute], symbols: &ThreadedRodeo) -> bool {
    // Check for #[test] attribute
    let test_name = symbols.get_or_intern("test");
    attributes.iter().any(|attr| attr.name == test_name)
}

#[tokio::test]
async fn test() -> Result<(), Error> {
    // Debug what directory we're looking in
    let current_dir = std::env::current_dir()?;
    println!("Current directory: {:?}", current_dir);
    
    let (hir_functions, hir_symbols, mir) = compile_source_with_tests_and_hir(PathBuf::from("..")).await?;

    println!("=== MIR ===");
    println!("{}", mir);

    let compiler = LowCompiler::new();
    let mut generator = compiler.create_code_generator()?;
    generator.generate(&mir)?;

    // Find all test functions from HIR (which has attributes)
    let mut test_functions = Vec::new();
    for (func_ref, func) in &hir_functions {
        let func_path = func_ref.reference.format_top(&hir_symbols, String::new())?;
        if is_test_function(&func.attributes, &hir_symbols) {
            test_functions.push(func_path);
        }
    }

    println!("=== Running {} tests ===", test_functions.len());
    
    let mut passed = 0;
    let mut failed = 0;
    
    for test_func in &test_functions {
        print!("test {} ... ", test_func);
        
        // SAFETY: Running external code is always unsafe.
        let result = unsafe {
            match generator.execute::<TestFunction>(test_func) {
                Ok(func) => func.call(),
                Err(_) => {
                    println!("FAILED (compilation error)");
                    failed += 1;
                    continue;
                }
            }
        };
        
        if result != 0 {
            println!("ok");
            passed += 1;
        } else {
            println!("FAILED");
            failed += 1;
        }
    }
    
    println!("\ntest result: {}. {} passed; {} failed", 
        if failed == 0 { "ok" } else { "FAILED" },
        passed, 
        failed
    );
    
    if failed > 0 {
        return Err(anyhow::anyhow!("{} tests failed", failed));
    }
    
    Ok(())
}
