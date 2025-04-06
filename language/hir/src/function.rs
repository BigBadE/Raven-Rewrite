use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::fmt::Debug;
use syntax::structure::traits::{Function, Terminator};
use syntax::structure::visitor::Translate;
use syntax::structure::{FileOwner, Modifier};
use syntax::util::path::FilePath;
use syntax::util::translation::Translatable;
use syntax::util::ParseError;
use syntax::SyntaxLevel;

#[derive(Serialize, Deserialize, Debug)]
pub struct CodeBlock<T: SyntaxLevel> {
    pub statements: Vec<T::Statement>,
    pub terminator: T::Terminator,
}

#[derive(Serialize, Deserialize, Debug)]
pub enum HighTerminator<T: SyntaxLevel> {
    Return(Option<T::Expression>),
    Break,
    Continue,
    None,
}

impl<T: SyntaxLevel> Terminator for HighTerminator<T> {}

#[derive(Serialize, Deserialize, Debug)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
pub struct HighFunction<T: SyntaxLevel> {
    pub name: Spur,
    pub file: FilePath,
    pub modifiers: Vec<Modifier>,
    pub parameters: Vec<(Spur, T::TypeReference)>,
    pub return_type: Option<T::TypeReference>,
    pub body: CodeBlock<T>,
}

impl<T: SyntaxLevel> Function for HighFunction<T> {
    fn file(&self) -> &FilePath {
        &self.file
    }
}

// Handle type translation
impl<C: FileOwner, I: SyntaxLevel + Translatable<C, I, O>, O: SyntaxLevel>
    Translate<HighFunction<O>, C, I, O> for HighFunction<I>
{
    fn translate(&self, context: &mut C) -> Result<HighFunction<O>, ParseError> {
        context.set_file(self.file.clone());
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
                    Ok::<_, ParseError>((name.clone(), I::translate_type_ref(ty, context)?))
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

impl<C: FileOwner, I: SyntaxLevel + Translatable<C, I, O>, O: SyntaxLevel>
    Translate<HighTerminator<O>, C, I, O> for HighTerminator<I>
{
    fn translate(&self, context: &mut C) -> Result<HighTerminator<O>, ParseError> {
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
