use indexmap::IndexMap;
use lasso::Spur;
use serde::{Deserialize, Serialize};
use syntax::structure::traits::{Function, Terminator};
use syntax::structure::visitor::Translate;
use syntax::structure::{Attribute, Modifier};
use syntax::util::translation::{translate_fields, translate_iterable, Translatable};
use syntax::util::CompileError;
use syntax::{ContextSyntaxLevel, SyntaxLevel};
use crate::{HighSyntaxLevel, HirFunctionContext};
use crate::types::HighType;

/// A function in the HIR
#[derive(Serialize, Deserialize, Clone)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
pub struct HighFunction<T: SyntaxLevel> {
    /// The reference (file path) to the function
    pub reference: T::FunctionReference,
    /// The attributes applied to the function (e.g., #[test])
    pub attributes: Vec<Attribute>,
    /// The modifiers of the function
    pub modifiers: Vec<Modifier>,
    /// The parameters of the function
    pub parameters: Vec<(Spur, T::TypeReference)>,
    /// The function's generics
    pub generics: IndexMap<Spur, Vec<T::TypeReference>>,
    /// The return type of the function
    pub return_type: Option<T::TypeReference>,
    /// The body of the function (None for trait function signatures)
    pub body: Option<CodeBlock<T>>,
}

/// A block of code
#[derive(Serialize, Deserialize, Clone)]
pub struct CodeBlock<T: SyntaxLevel> {
    /// The statements in the block
    pub statements: Vec<T::Statement>,
    /// The terminator of the block
    pub terminator: T::Terminator,
}

/// A terminator for a block of code
#[derive(Serialize, Deserialize, Clone)]
pub enum HighTerminator<T: SyntaxLevel> {
    /// A return statement
    Return(Option<T::Expression>),
    /// A break statement
    Break,
    /// A continue statement
    Continue,
    /// No terminator
    None,
}

impl<T: SyntaxLevel> Terminator for HighTerminator<T> {
    fn is_none(&self) -> bool {
        match self {
            HighTerminator::None => true,
            _ => false,
        }
    }
}

impl<T: SyntaxLevel> Function<T::FunctionReference> for HighFunction<T> {
    fn reference(&self) -> &T::FunctionReference {
        &self.reference
    }
}

// Handle type translation
impl<'ctx, I: SyntaxLevel<Type = HighType<I>, Function = HighFunction<I>> + Translatable<I, HighSyntaxLevel>>
Translate<(), HirFunctionContext<'ctx>> for HighFunction<I>
{
    fn translate(
        &self,
        context: &mut HirFunctionContext<'_>,
    ) -> Result<(), CompileError> {
        let function_ref = I::translate_func_ref(&self.reference, context)?;

        let function = HighFunction::<HighSyntaxLevel> {
            reference: function_ref,
            attributes: self.attributes.clone(),
            modifiers: self.modifiers.clone(),
            body: match &self.body {
                Some(body) => Some(CodeBlock {
                    statements: translate_iterable(&body.statements, context, I::translate_stmt)?,
                    terminator: I::translate_terminator(&body.terminator, context)?,
                }),
                None => None,
            },
            parameters: translate_fields(&self.parameters, context, I::translate_type_ref)?,
            generics: translate_iterable(&self.generics, context,
                                         |(key, types), context|
                                             Ok((*key, translate_iterable(types, context, I::translate_type_ref)?)))?,
            return_type: self
                .return_type
                .as_ref()
                .map(|ty| I::translate_type_ref(ty, context))
                .transpose()?,
        };
        
        context.syntax.functions.insert(function.reference.clone(), function);
        Ok(())
    }
}

impl<'ctx, I: SyntaxLevel + Translatable<I, O>, O: ContextSyntaxLevel<I>>
Translate<HighTerminator<O>, O::InnerContext<'ctx>> for HighTerminator<I>
{
    fn translate(
        &self,
        context: &mut O::InnerContext<'_>,
    ) -> Result<HighTerminator<O>, CompileError> {
        Ok(match self {
            HighTerminator::Return(expression) => HighTerminator::Return(
                expression
                    .as_ref()
                    .map(|expr| I::translate_expr(expr, context))
                    .transpose()?,
            ),
            HighTerminator::Break => HighTerminator::Break,
            HighTerminator::Continue => HighTerminator::Continue,
            HighTerminator::None => HighTerminator::None,
        })
    }
}
