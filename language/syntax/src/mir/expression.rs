use crate::code::literal::Literal;
use crate::hir::expression::{Expression, HighExpression};
use crate::mir::{FieldId, MirContext, Operand};
use crate::structure::visitor::Translate;
use crate::util::translation::Translatable;
use crate::util::ParseError;
use crate::SyntaxLevel;

#[derive(Debug)]
pub enum MediumExpression<T: SyntaxLevel> {
    Use(Operand),
    Literal(Literal),
    FunctionCall {
        func: T::FunctionReference,
        args: Vec<Operand>,
    },
    CreateStruct {
        struct_type: T::TypeReference,
        fields: Vec<(FieldId, Operand)>,
    },
}

impl<T: SyntaxLevel> Expression for MediumExpression<T> {}

// Handle statement translation
impl<I: SyntaxLevel + Translatable<MirContext, I, O>, O: SyntaxLevel>
Translate<MediumExpression<O>, MirContext, I, O> for HighExpression<I>
{
    fn translate(&self, _context: &mut MirContext) -> Result<MediumExpression<O>, ParseError> {
        match self {
            HighExpression::Literal(_literal) => {}
            HighExpression::CodeBlock(_block) => {}
            HighExpression::Variable(_variable) => {}
            HighExpression::Assignment { declaration, variable, value } => {}
            HighExpression::FunctionCall { function, target, arguments } => {}
            HighExpression::CreateStruct { target_struct, fields } => {}
        }
        Ok(MediumExpression::Literal(Literal::Void))
    }
}