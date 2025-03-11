use std::path::PathBuf;
use anyhow::Error;
use runner::compile_source;

#[tokio::main]
async fn main() -> Result<(), Error> {
    let syntax = match compile_source(PathBuf::from("tests/core")).await {
        Ok(syntax) => syntax,
        Err(errors) => {
            for err in errors {
                println!("{}", err);
            }
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