use crate::statement::FunctionGenerator;
use anyhow::{Context, Error};
use inkwell::values::BasicValueEnum;
use mir::expression::MediumExpression;
use mir::{MediumSyntaxLevel, Operand};
use syntax::structure::literal::Literal;

pub fn compile_expression<'a, 'b, 'ctx>(
    function_generator: &mut FunctionGenerator<'a, 'b, 'ctx>,
    expression: &MediumExpression<MediumSyntaxLevel>,
) -> Result<BasicValueEnum<'ctx>, Error> {
    Ok(match expression {
        MediumExpression::Use(operand) => compile_operand(function_generator, operand)?,
        MediumExpression::Literal(literal) => compile_literal(function_generator, literal)?,
        MediumExpression::FunctionCall { func, args } => {
            let func = function_generator.type_manager.function_type(func);
            let args = args
                .iter()
                .map(|arg| compile_operand(function_generator, arg).map(|value| value.into()))
                .collect::<Result<Vec<_>, Error>>()?;
            function_generator
                .builder()
                .build_call(func, args.as_slice(), "func_call")?
                .try_as_basic_value()
                .left()
                .context("Expected non-void function")?
        }
        MediumExpression::CreateStruct {
            struct_type,
            fields,
        } => {
            let struct_type = function_generator.type_manager.convert_type(*struct_type);

            let alloc = function_generator.builder().build_alloca(struct_type, "struct_init")?;
            for (i, (_, field)) in fields.iter().enumerate() {
                let field = compile_operand(function_generator, field)?;
                let field_ptr = function_generator
                    .builder()
                    .build_struct_gep(struct_type, alloc, i as u32, "struct_field")?;
                function_generator.builder().build_store(field_ptr, field)?;
            }

            alloc.into()
            // TODO make sure this drops correctly
        }
    })
}

pub fn compile_operand<'a, 'b, 'ctx>(
    function_generator: &mut FunctionGenerator<'a, 'b, 'ctx>,
    operand: &Operand,
) -> Result<BasicValueEnum<'ctx>, Error> {
    Ok(match operand {
        Operand::Copy(target) => {
            let (pointer, types) = function_generator.variables[&target.local];
            function_generator
                .builder()
                .build_load(types, pointer, "")?
        }
        Operand::Move(target) => {
            let (pointer, types) = function_generator.variables[&target.local];
            function_generator
                .builder()
                .build_load(types, pointer, "")?
            // TODO handle dropping semantics
        }
        Operand::Constant(literal) => compile_literal(function_generator, literal)?,
    })
}

pub fn compile_literal<'a, 'b, 'ctx>(
    function_generator: &mut FunctionGenerator<'a, 'b, 'ctx>,
    literal: &Literal,
) -> Result<BasicValueEnum<'ctx>, Error> {
    Ok(match literal {
        Literal::String(string) => {
            let string = function_generator
                .type_manager
                .syntax
                .symbols
                .resolve(string);
            let string = string
                .chars()
                .map(|char| {
                    function_generator
                        .type_manager
                        .context
                        .i8_type()
                        .const_int(char as u64, false)
                })
                .collect::<Vec<_>>();
            function_generator
                .type_manager
                .context
                .i8_type()
                .const_array(string.as_slice())
                .into()
        }
        Literal::F64(float) => function_generator
            .type_manager
            .context
            .f64_type()
            .const_float(*float)
            .into(),
        Literal::F32(float) => function_generator
            .type_manager
            .context
            .f32_type()
            .const_float(*float as f64)
            .into(),
        Literal::I64(int) => function_generator
            .type_manager
            .context
            .i64_type()
            .const_int(*int as u64, false)
            .into(),
        Literal::I32(int) => function_generator
            .type_manager
            .context
            .i32_type()
            .const_int(*int as u64, false)
            .into(),
        Literal::U64(uint) => function_generator
            .type_manager
            .context
            .i64_type()
            .const_int(*uint, false)
            .into(),
        Literal::U32(uint) => function_generator
            .type_manager
            .context
            .i32_type()
            .const_int(*uint as u64, false)
            .into(),
        Literal::Bool(bool) => function_generator
            .type_manager
            .context
            .bool_type()
            .const_int(*bool as u64, false)
            .into(),
        Literal::Char(char) => function_generator
            .type_manager
            .context
            .i8_type()
            .const_int(*char as u64, false)
            .into(),
    })
}
