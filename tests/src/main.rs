use anyhow::Error;
use runner::compile_source;
use std::path::PathBuf;
use compiler_llvm::LowCompiler;

type Main = unsafe extern "C" fn () -> i32;

#[tokio::main]
async fn main() -> Result<(), Error> {

    let syntax = match compile_source(PathBuf::from("tests/core")).await {
        Ok(syntax) => syntax,
        Err(errors) => {
            println!("{}", errors);
            return Ok(());
        }
    };
    for types in &syntax.types {
        println!("{:#?}", types);
    }
    for function in &syntax.functions {
        println!("{:#?}", function);
    }
    let mut compiler = LowCompiler::new();
    let mut generator = compiler.create_code_generator()?;
    generator.generate(&syntax);
    unsafe {
        let value: i32 = generator.execute::<Main>("test")?.call();
    }
    Ok(())
}
