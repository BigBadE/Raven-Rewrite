use std::collections::HashMap;
use crate::hir::function::{CodeBlock, Function, HighFunction};
use crate::mir::{LocalVar, MediumSyntaxLevel, MediumTerminator, MirContext};
use crate::structure::visitor::{FileOwner, Translate};
use crate::util::translation::Translatable;
use crate::util::ParseError;
use crate::SyntaxLevel;
use std::mem;
use lasso::Spur;
use crate::structure::Modifier;
use crate::util::path::FilePath;

#[derive(Debug)]
pub struct MediumFunction<T: SyntaxLevel> {
    pub name: Spur,
    pub file: FilePath,
    pub modifiers: Vec<Modifier>,
    pub parameters: Vec<T::TypeReference>,
    pub return_type: Option<T::TypeReference>,
    pub body: Vec<CodeBlock<T>>,
    pub local_vars: HashMap<Spur, LocalVar>,
}

impl<T: SyntaxLevel> Function for MediumFunction<T> {
    fn file(&self) -> &FilePath {
        self.file.as_ref()
    }
}
impl<'a, I: SyntaxLevel + Translatable<MirContext<'a>, I, MediumSyntaxLevel>>
    Translate<MediumFunction<MediumSyntaxLevel>, MirContext<'_>, I, MediumSyntaxLevel> for HighFunction<I>
{
    fn translate(&self, context: &mut MirContext) -> Result<MediumFunction<MediumSyntaxLevel>, ParseError> {
        context.set_file(self.file.clone());
        for statement in &self.body.statements {
            I::translate_stmt(statement, context)?;
        }

        // Return void if we have no return at the very end
        if let MediumTerminator::Unreachable = context.code_blocks[context.current_block].terminator {
            context.set_terminator(MediumTerminator::Return(None));
        }

        Ok(MediumFunction {
            name: self.name,
            file: self.file.clone(),
            modifiers: self.modifiers.clone(),
            body: mem::take(&mut context.code_blocks),
            local_vars: mem::take(&mut context.local_vars),
            parameters: self
                .parameters
                .iter()
                .map(|(name, ty)| {
                    Ok::<_, ParseError>(I::translate_type_ref(ty, context)?)
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
