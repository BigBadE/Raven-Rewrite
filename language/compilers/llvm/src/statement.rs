use crate::expression::{compile_expression, compile_literal, compile_operand};
use crate::types::TypeManager;
use anyhow::Error;
use hir::function::CodeBlock;
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::types::BasicTypeEnum;
use inkwell::values::{BasicValue, PointerValue};
use mir::statement::MediumStatement;
use mir::{LocalVar, MediumSyntaxLevel, MediumTerminator};
use std::collections::HashMap;

/// Holds the state of the function being generated
pub struct FunctionGenerator<'a, 'b, 'ctx> {
    /// Manages converting types
    pub type_manager: &'a mut TypeManager<'b, 'ctx>,
    /// The variables in the function
    pub variables: HashMap<LocalVar, (PointerValue<'ctx>, BasicTypeEnum<'ctx>)>,
    /// The blocks in the function
    pub blocks: Vec<BasicBlock<'ctx>>,
}

impl<'a, 'b, 'ctx> FunctionGenerator<'a, 'b, 'ctx> {
    /// Gets the builder
    pub fn builder(&mut self) -> &Builder<'ctx> {
        &self.type_manager.builder
    }
}

/// Compiles a block of code
pub fn compile_block<'ctx>(
    function_generator: &mut FunctionGenerator,
    block: &CodeBlock<MediumSyntaxLevel>,
) -> Result<(), Error> {
    for statement in &block.statements {
        compile_statement(function_generator, statement)?;
    }
    match &block.terminator {
        MediumTerminator::Goto(target) => {
            let target = function_generator.blocks[*target];
            function_generator
                .builder()
                .build_unconditional_branch(target)?;
        }
        MediumTerminator::Switch {
            discriminant,
            targets,
            fallback,
        } => {
            let discriminant = compile_expression(function_generator, discriminant)?;
            let fallback = function_generator.blocks[*fallback];
            let targets = targets
                .iter()
                .map(|(target, block)| {
                    Ok::<_, Error>((
                        compile_literal(function_generator, target)?.into_int_value(),
                        function_generator.blocks[*block],
                    ))
                })
                .collect::<Result<Vec<_>, _>>()?;
            function_generator.builder().build_switch(
                discriminant.into_int_value(),
                fallback,
                targets.as_slice(),
            )?;
        }
        MediumTerminator::Return(returning) => {
            match returning
                .as_ref()
                .map(|inner| compile_expression(function_generator, inner))
                .transpose()?
            {
                Some(returning) => {
                    let returning: Option<&dyn BasicValue> = Some(&returning);
                    function_generator.builder().build_return(returning)?;
                }
                None => {
                    function_generator.builder().build_return(None)?;
                }
            }
        }
        MediumTerminator::Unreachable => {
            function_generator.builder().build_unreachable()?;
        }
    }
    Ok(())
}

/// Compiles a statement
pub fn compile_statement<'ctx>(
    function_generator: &mut FunctionGenerator,
    statement: &MediumStatement<MediumSyntaxLevel>,
) -> Result<(), Error> {
    match statement {
        MediumStatement::Assign { place, value } => {
            let target = function_generator.variables[&place.local].0;
            let value = compile_expression(function_generator, value)?;
            function_generator.builder().build_store(target, value)?;
        }
        MediumStatement::StorageLive(local, types) => {
            let types = function_generator.type_manager.convert_type(types);
            let pointer = function_generator.builder().build_alloca(types, "")?;
            function_generator
                .variables
                .insert(*local, (pointer, types));
        }
        MediumStatement::StorageDead(local) => {
            let pointer = function_generator.variables[&local].0;
            function_generator.builder().build_free(pointer)?;
            // TODO handle dropping semantics
        }
        MediumStatement::Call { function, args } => {
            // Handle void function calls directly without creating dummy variables
            let func = function_generator.type_manager.function_type(function);
            let args = args
                .iter()
                .map(|arg| compile_operand(function_generator, arg).map(|value| value.into()))
                .collect::<Result<Vec<_>, Error>>()?;
            function_generator
                .builder()
                .build_call(func, args.as_slice(), "void_call")?;
            // Note: We ignore the result since this is a void call
        }
        MediumStatement::Noop => {}
    }
    Ok(())
}
