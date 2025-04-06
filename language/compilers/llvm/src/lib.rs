mod expression;
mod function;
mod statement;
mod types;

use crate::statement::{compile_block, FunctionGenerator};
use crate::types::TypeManager;
use anyhow::Error;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, JitFunction, UnsafeFunctionPointer};
use inkwell::module::Module;
use inkwell::OptimizationLevel;
use mir::MediumSyntaxLevel;
use std::collections::HashMap;
use syntax::{FunctionRef, Syntax};

pub struct LowCompiler {
    context: Context,
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
            execution_engine: module
                .create_jit_execution_engine(OptimizationLevel::None)
                .map_err(|err| Error::msg(err.to_string()))?,
            module,
            builder: self.context.create_builder(),
        })
    }
}

#[derive(Debug)]
pub struct LowSyntaxLevel;

impl<'ctx> CodeGenerator<'ctx> {
    pub fn generate(&mut self, code: &'ctx Syntax<MediumSyntaxLevel>) -> Result<(), Error> {
        let mut type_manager = TypeManager {
            syntax: code,
            context: &self.context,
            module: &self.module,
            builder: &self.builder,
            types: HashMap::default(),
            functions: HashMap::default(),
        };

        for (reference, function) in code.functions.iter().enumerate() {
            let mut blocks = Vec::new();
            for (position, _) in function.body.iter().enumerate() {
                let function = type_manager.function_type(&FunctionRef(reference));
                blocks.push(
                    type_manager
                        .context
                        .append_basic_block(function, &format!("{position}")),
                );
            }

            let mut function_generator = FunctionGenerator {
                type_manager: &mut type_manager,
                variables: HashMap::default(),
                blocks,
            };

            for (position, block) in function.body.iter().enumerate() {
                let target = function_generator.blocks[position];
                function_generator.builder().position_at_end(target);
                compile_block(&mut function_generator, block)?;
            }
        }
        Ok(())
    }

    pub fn execute<F: UnsafeFunctionPointer>(
        &mut self,
        function: &str,
    ) -> Result<JitFunction<F>, Error> {
        // SAFETY: We assume the caller knows that it's calling user-generated code
        unsafe { Ok(self.execution_engine.get_function(function)?) }
    }
}
