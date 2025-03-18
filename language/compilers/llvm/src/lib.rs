use anyhow::Error;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, JitFunction, UnsafeFunctionPointer};
use inkwell::module::Module;
use inkwell::OptimizationLevel;
use syntax::mir::MediumSyntaxLevel;
use syntax::Syntax;

pub struct LowCompiler {
    context: Context
}

pub struct CodeGenerator<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    execution_engine: ExecutionEngine<'ctx>,
}

impl LowCompiler {
    pub fn new() -> Self {
        let context = Context::create();
        Self { context }
    }

    pub fn create_code_generator(&self) -> Result<CodeGenerator, Error> {
        let module = self.context.create_module("main");
        Ok(CodeGenerator {
            context: &self.context,
            execution_engine: module.create_jit_execution_engine(OptimizationLevel::None).map_err(|err| Error::msg(err.to_string()))?,
            module,
            builder: self.context.create_builder(),
        })
    }
}

impl CodeGenerator<'_> {
    pub fn generate(&mut self, code: Syntax<MediumSyntaxLevel>) {

    }

    pub fn execute<F: UnsafeFunctionPointer>(&mut self, function: &str) -> Result<JitFunction<F>, Error> {
        unsafe {
            Ok(self.execution_engine.get_function(function)?)
        }
    }
}