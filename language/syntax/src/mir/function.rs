use lasso::Spur;
use crate::hir::function::{Function, HighFunction};
use crate::mir::MirContext;
use crate::structure::Modifier;
use crate::structure::visitor::{FileOwner, Translate};
use crate::SyntaxLevel;
use crate::util::ParseError;
use crate::util::path::FilePath;
use crate::util::translation::Translatable;

#[derive(Debug)]
pub struct MediumFunction<T: SyntaxLevel> {
    pub name: Spur,
    pub file: FilePath,
    pub modifiers: Vec<Modifier>,
    pub parameters: Vec<(Spur, T::TypeReference)>,
    pub return_type: Option<T::TypeReference>,
    pub body: T::Statement,
}

impl<T: SyntaxLevel> Function for MediumFunction<T> {
    fn file(&self) -> &FilePath {
        &self.file
    }
}

// Handle type translation
impl<I: SyntaxLevel + Translatable<MirContext, I, O>, O: SyntaxLevel> Translate<MediumFunction<O>, MirContext, I, O>
for HighFunction<I> {
    fn translate(&self, context: &mut MirContext) -> Result<MediumFunction<O>, ParseError> {
        context.set_file(self.file.clone());
        Ok(MediumFunction {
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
