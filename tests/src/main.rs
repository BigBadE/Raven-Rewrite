use anyhow::Error;
use runner::compile_source;
use std::path::PathBuf;

#[tokio::main]
async fn main() -> Result<(), Error> {
    let syntax = match compile_source(PathBuf::from("tests/core")).await {
        Ok(syntax) => syntax,
        Err(errors) => {
            println!("{}", errors);
            return Ok(());
        }
    };
    for types in syntax.types {
        println!("{:?}", types);
    }
    for function in syntax.functions {
        println!("{:?}", function);
    }
    Ok(())
}
