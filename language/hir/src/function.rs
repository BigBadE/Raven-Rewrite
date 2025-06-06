use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt::Debug;
use syntax::structure::traits::{Function, Terminator};
use syntax::structure::visitor::Translate;
use syntax::structure::Modifier;
use syntax::util::path::FilePath;
use syntax::util::translation::{translate_fields, translate_map, translate_vec, Translatable};
use syntax::util::CompileError;
use syntax::{ContextSyntaxLevel, SyntaxLevel};

/// A function in the HIR
#[derive(Serialize, Deserialize, Debug)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
pub struct HighFunction<T: SyntaxLevel> {
    /// The name of the function
    pub name: Spur,
    /// The file the function is in
    pub file: FilePath,
    /// The modifiers of the function
    pub modifiers: Vec<Modifier>,
    /// The parameters of the function
    pub parameters: Vec<(Spur, T::TypeReference)>,
    /// The function's generics
    pub generics: HashMap<Spur, Vec<T::TypeReference>>,
    /// The return type of the function
    pub return_type: Option<T::TypeReference>,
    /// The body of the function
    pub body: CodeBlock<T>,
}

/// A block of code
#[derive(Serialize, Deserialize, Debug)]
pub struct CodeBlock<T: SyntaxLevel> {
    /// The statements in the block
    pub statements: Vec<T::Statement>,
    /// The terminator of the block
    pub terminator: T::Terminator,
}

/// A terminator for a block of code
#[derive(Serialize, Deserialize, Debug)]
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

impl<T: SyntaxLevel> Terminator for HighTerminator<T> {}

impl<T: SyntaxLevel> Function for HighFunction<T> {
    fn file(&self) -> &FilePath {
        &self.file
    }
}

// Handle type translation
impl<'ctx, I: SyntaxLevel + Translatable<I, O>, O: ContextSyntaxLevel<I>>
    Translate<HighFunction<O>, O::InnerContext<'ctx>> for HighFunction<I>
{
    fn translate(
        &self,
        context: &mut O::InnerContext<'_>,
    ) -> Result<HighFunction<O>, CompileError> {
        Ok(HighFunction {
            name: self.name,
            file: self.file.clone(),
            modifiers: self.modifiers.clone(),
            body: CodeBlock {
                statements: translate_vec(&self.body.statements, context, I::translate_stmt)?,
                terminator: I::translate_terminator(&self.body.terminator, context)?,
            },
            parameters: translate_fields(&self.parameters, context, I::translate_type_ref)?,
            generics: translate_map(&self.generics, context,
                                    |types, context| translate_vec(types, context, I::translate_type_ref))?,
            return_type: self
                .return_type
                .as_ref()
                .map(|ty| I::translate_type_ref(ty, context))
                .transpose()?,
        })
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
