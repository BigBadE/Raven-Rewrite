mod function;
mod type_manager;
mod statement;

use crate::type_manager::TypeManager;
use anyhow::Error;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, JitFunction, UnsafeFunctionPointer};
use inkwell::module::Module;
use inkwell::types::BasicType;
use inkwell::OptimizationLevel;
use std::collections::HashMap;
use syntax::mir::MediumSyntaxLevel;
use syntax::Syntax;

pub struct LowCompiler {
    context: Context
}

pub struct CodeGenerator<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    execution_engine: ExecutionEngine<'ctx>
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
            builder: self.context.create_builder()
        })
    }
}

#[derive(Debug)]
pub struct LowSyntaxLevel;

impl<'ctx> CodeGenerator<'ctx> {
    pub fn generate(&mut self, code: &'ctx Syntax<MediumSyntaxLevel>) {
        let mut type_manager = TypeManager {
            syntax: code,
            context: &self.context,
            types: HashMap::default()
        };
        for function in &code.functions {
            let parameters = function.parameters.iter()
                .map(|param| type_manager.convert_type(*param).into())
                .collect::<Vec<_>>();
            let parameters = parameters.as_slice();
            let function_val = self.module.add_function(code.symbols.resolve(&function.name),
                                     function.return_type
                                         .map(|inner| type_manager.convert_type(inner).fn_type(parameters, false))
                                         .unwrap_or(self.context.void_type().fn_type(parameters, false)), None);

            let mut blocks = Vec::new();
            for (position, _) in &function.body.iter().enumerate() {
                blocks.push(self.context.append_basic_block(function_val, &format!("{position}")));
            }
            for (position, block) in &function.body.iter().enumerate() {
                self.builder.position_at_end(block[position]);

            }
        }
    }

    pub fn execute<F: UnsafeFunctionPointer>(&mut self, function: &str) -> Result<JitFunction<F>, Error> {
        // SAFETY: We assume the caller knows that it's calling user-generated code
        unsafe {
            Ok(self.execution_engine.get_function(function)?)
        }
    }
}