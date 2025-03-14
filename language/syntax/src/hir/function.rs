use crate::structure::visitor::{FileOwner, Translate};
use crate::structure::Modifier;
use crate::util::path::FilePath;
use crate::util::translation::Translatable;
use crate::util::ParseError;
use crate::SyntaxLevel;
use lasso::Spur;
use std::fmt::Debug;

pub trait Function: Debug {
    fn file(&self) -> &FilePath;
}

pub trait FunctionReference: Debug {}

#[derive(Debug)]
pub struct HighFunction<T: SyntaxLevel> {
    pub name: Spur,
    pub file: FilePath,
    pub modifiers: Vec<Modifier>,
    pub parameters: Vec<(Spur, T::TypeReference)>,
    pub return_type: Option<T::TypeReference>,
    pub body: T::Statement,
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
            body: I::translate_stmt(&self.body, context)?,
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
