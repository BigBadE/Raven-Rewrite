use std::path::PathBuf;
use anyhow::Error;
use runner::{compile_source, ParseError};

#[tokio::main]
async fn main() -> Result<(), Error> {
    let syntax = match compile_source(PathBuf::from("tests/core")).await {
        Ok(syntax) => syntax,
        Err(ParseError::ParseError(err)) => {
            println!("{}", err);
            return Ok(());
        }
        Err(ParseError::InternalError(e)) => return Err(e),
    };
    for function in syntax.functions {
        println!("{:?}", function);
    }
    Ok(())
}