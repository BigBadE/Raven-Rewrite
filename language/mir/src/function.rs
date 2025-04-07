use crate::{MediumSyntaxLevel, MediumTerminator, MirFunctionContext};
use hir::function::{CodeBlock, HighFunction};
use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::mem;
use syntax::SyntaxLevel;
use syntax::structure::Modifier;
use syntax::structure::traits::Function;
use syntax::structure::visitor::Translate;
use syntax::util::CompileError;
use syntax::util::path::FilePath;
use syntax::util::translation::Translatable;

/// A function in the MIR.
#[derive(Serialize, Deserialize, Debug)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
pub struct MediumFunction<T: SyntaxLevel> {
    /// The function's name
    pub name: Spur,
    /// The file path where the function is defined
    pub file: FilePath,
    /// The modifiers of the function
    pub modifiers: Vec<Modifier>,
    /// The parameters of the function
    pub parameters: Vec<T::TypeReference>,
    /// The return type of the function
    pub return_type: Option<T::TypeReference>,
    /// The body of the function
    pub body: Vec<CodeBlock<T>>,
}

impl<T: SyntaxLevel> Function for MediumFunction<T> {
    fn file(&self) -> &FilePath {
        &self.file
    }
}

impl<'a, I: SyntaxLevel + Translatable<MirFunctionContext<'a>, I, MediumSyntaxLevel>>
    Translate<MediumFunction<MediumSyntaxLevel>, MirFunctionContext<'a>> for HighFunction<I>
{
    fn translate(
        &self,
        context: &mut MirFunctionContext<'a>,
    ) -> Result<MediumFunction<MediumSyntaxLevel>, CompileError> {
        for statement in &self.body.statements {
            I::translate_stmt(statement, context)?;
        }

        // Return void if we have no return at the very end
        if matches!(
            context.code_blocks[context.current_block].terminator,
            MediumTerminator::Unreachable
        ) {
            context.set_terminator(MediumTerminator::Return(None));
        }

        Ok(MediumFunction {
            name: self.name,
            file: self.file.clone(),
            modifiers: self.modifiers.clone(),
            body: mem::take(&mut context.code_blocks),
            parameters: self
                .parameters
                .iter()
                .map(|(_, ty)| Ok::<_, CompileError>(I::translate_type_ref(ty, context)?))
                .collect::<Result<_, _>>()?,
            return_type: self
                .return_type
                .as_ref()
                .map(|ty| I::translate_type_ref(ty, context))
                .transpose()?,
        })
    }
}
