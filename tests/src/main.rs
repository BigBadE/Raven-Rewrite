use anyhow::Error;
use compiler_llvm::LowCompiler;
use runner::compile_source;
use std::path::PathBuf;

type Main = unsafe extern "C" fn() -> i32;

fn main() {}

#[tokio::test]
async fn test() -> Result<(), Error> {
    let syntax = match compile_source(PathBuf::from("core")).await {
        Ok(syntax) => syntax,
        Err(errors) => return Err(Error::from(errors)),
    };

    let compiler = LowCompiler::new();
    let mut generator = compiler.create_code_generator()?;
    generator.generate(&syntax)?;

    // SAFETY: Running external code is always unsafe.
    unsafe {
        println!("{}", generator.execute::<Main>("test")?.call());
    }
    Ok(())
}
