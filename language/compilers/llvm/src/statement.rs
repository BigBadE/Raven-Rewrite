use crate::expression::{compile_expression, compile_literal};
use crate::types::TypeManager;
use anyhow::Error;
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::values::{BasicValue, PointerValue};
use std::collections::HashMap;
use inkwell::types::BasicTypeEnum;
use hir::function::CodeBlock;
use mir::statement::MediumStatement;
use mir::{LocalVar, MediumSyntaxLevel, MediumTerminator};

pub struct FunctionGenerator<'a, 'b, 'ctx> {
    pub type_manager: &'a mut TypeManager<'b, 'ctx>,
    pub variables: HashMap<LocalVar, (PointerValue<'ctx>, BasicTypeEnum<'ctx>)>,
    pub blocks: Vec<BasicBlock<'ctx>>,
}

impl<'a, 'b, 'ctx> FunctionGenerator<'a, 'b, 'ctx> {
    pub fn builder(&mut self) -> &Builder<'ctx> {
        &self.type_manager.builder
    }
}

pub fn compile_block<'ctx>(function_generator: &mut FunctionGenerator, block: &CodeBlock<MediumSyntaxLevel>) -> Result<(), Error> {
    for statement in &block.statements {
        compile_statement(function_generator, statement)?;
    }
    match &block.terminator {
        MediumTerminator::Goto(target) => {
            let target = function_generator.blocks[*target];
            function_generator.builder().build_unconditional_branch(target)?;
        }
        MediumTerminator::Switch { discriminant, targets, fallback } => {
            let discriminant = compile_expression(function_generator, discriminant)?;
            let fallback = function_generator.blocks[*fallback];
            let targets = targets.iter()
                .map(|(target, block)|
                    Ok::<_, Error>((compile_literal(function_generator, target)?.into_int_value(), function_generator.blocks[*block])))
                .collect::<Result<Vec<_>, _>>()?;
            function_generator.builder()
                .build_switch(discriminant.into_int_value(), fallback,
                              targets.as_slice())?;
        }
        MediumTerminator::Return(returning) => {
            match returning.as_ref()
                .map(|inner| compile_expression(function_generator, inner))
                .transpose()? {
                Some(returning) => {
                    let returning: Option<&dyn BasicValue> = Some(&returning);
                    function_generator.builder().build_return(returning)?;
                },
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

pub fn compile_statement<'ctx>(function_generator: &mut FunctionGenerator, statement: &MediumStatement<MediumSyntaxLevel>) -> Result<(), Error> {
    match statement {
        MediumStatement::Assign { place, value } => {
            let target = function_generator.variables[&place.local].0;
            let value = compile_expression(function_generator, value)?;
            function_generator.builder().build_store(target, value)?;
        }
        MediumStatement::StorageLive(local, types) => {
            let types = function_generator.type_manager.convert_type(*types);
            let pointer = function_generator.builder().build_alloca(
                types, "")?;
            function_generator.variables.insert(*local, (pointer, types));
        }
        MediumStatement::StorageDead(local) => {
            let pointer = function_generator.variables[&local].0;
            function_generator.builder().build_free(pointer)?;
            // TODO handle dropping semantics
        }
        MediumStatement::Noop => {}
    }
    Ok(())
}