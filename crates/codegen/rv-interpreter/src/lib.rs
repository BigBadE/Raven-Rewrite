//! MIR bytecode interpreter
//!
//! Fast interpreter for executing MIR during development.
//! Slower than Cranelift/LLVM but has instant startup time.

pub mod interpreter;
pub mod value;

pub use interpreter::{Interpreter, InterpreterError};
pub use value::Value;
