use crate::hir::function::{Function, HighFunction};
use crate::mir::MirContext;
use crate::structure::visitor::{FileOwner, Translate};
use crate::structure::Modifier;
use crate::util::path::FilePath;
use crate::util::translation::Translatable;
use crate::util::ParseError;
use crate::SyntaxLevel;
use lasso::Spur;

#[derive(Debug)]
pub struct MediumFunction<T: SyntaxLevel> {
    pub name: Spur,
    pub file: FilePath,
    pub modifiers: Vec<Modifier>,
    pub parameters: Vec<(Spur, T::TypeReference)>,
    pub return_type: Option<T::TypeReference>,
    pub body: Vec<T::Statement>,
}

impl<T: SyntaxLevel> Function for MediumFunction<T> {
    fn file(&self) -> &FilePath {
        &self.file
    }
}

// Handle type translation
impl<I: SyntaxLevel + Translatable<MirContext, I, O>, O: SyntaxLevel>
    Translate<MediumFunction<O>, MirContext, I, O> for HighFunction<I>
{
    fn translate(&self, context: &mut MirContext) -> Result<MediumFunction<O>, ParseError> {
        context.set_file(self.file.clone());
        context.next_block = 1;
        // The tree must be flattened into a list with a depth-first traversal
        let mut body = vec!(I::translate_stmt(&self.body, context)?);
        body.append(&mut context.adding_blocks);
        Ok(MediumFunction {
            name: self.name,
            file: self.file.clone(),
            modifiers: self.modifiers.clone(),
            body,
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
