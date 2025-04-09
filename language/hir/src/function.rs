use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::fmt::Debug;
use syntax::structure::traits::{Function, Terminator};
use syntax::structure::visitor::Translate;
use syntax::structure::Modifier;
use syntax::util::path::FilePath;
use syntax::util::translation::Translatable;
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
impl<'ctx, I: SyntaxLevel + Translatable<I, O>, O: ContextSyntaxLevel>
    Translate<HighFunction<O>, O::FunctionContext<'ctx>> for HighFunction<I>
{
    fn translate(&self, context: &mut O::FunctionContext<'_>) -> Result<HighFunction<O>, CompileError> {
        Ok(HighFunction {
            name: self.name,
            file: self.file.clone(),
            modifiers: self.modifiers.clone(),
            body: CodeBlock {
                statements: self
                    .body
                    .statements
                    .iter()
                    .map(|statement| I::translate_stmt(&statement, context))
                    .collect::<Result<_, _>>()?,
                terminator: I::translate_terminator(&self.body.terminator, context)?,
            },
            parameters: self
                .parameters
                .iter()
                .map(|(name, ty)| {
                    Ok::<_, CompileError>((name.clone(), I::translate_type_ref(ty, context)?))
                })
                .collect::<Result<_, _>>()?,
            return_type: self
                .return_type
                .as_ref()
                .map(|ty| I::translate_type_ref(ty, context))
                .transpose()?,
        })
    }
}

impl<'ctx, I: SyntaxLevel + Translatable<I, O>, O: ContextSyntaxLevel>
    Translate<HighTerminator<O>, O::FunctionContext<'ctx>> for HighTerminator<I>
{
    fn translate(&self, context: &mut O::FunctionContext<'_>) -> Result<HighTerminator<O>, CompileError> {
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
