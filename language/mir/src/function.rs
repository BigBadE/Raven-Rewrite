use std::collections::HashMap;
use hir::function::{CodeBlock, HighFunction};
use crate::{LocalVar, MediumSyntaxLevel, MediumTerminator, MirContext};
use syntax::structure::visitor::Translate;
use syntax::util::translation::Translatable;
use syntax::util::ParseError;
use syntax::SyntaxLevel;
use std::mem;
use lasso::Spur;
use serde::{Deserialize, Serialize};
use syntax::structure::{FileOwner, Modifier};
use syntax::structure::traits::Function;
use syntax::util::path::FilePath;

#[derive(Serialize, Deserialize, Debug)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
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
    Translate<MediumFunction<MediumSyntaxLevel>, MirContext<'a>, I, MediumSyntaxLevel> for HighFunction<I>
{
    fn translate(&self, context: &mut MirContext<'a>) -> Result<MediumFunction<MediumSyntaxLevel>, ParseError> {
        context.set_file(self.file.clone());
        context.reset();
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
                .map(|(_, ty)| {
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
