use crate::{MediumSyntaxLevel, MediumTerminator, MirFunctionContext};
use hir::function::{CodeBlock, HighFunction};
use serde::{Deserialize, Serialize};
use std::mem;
use hir::HighSyntaxLevel;
use syntax::{FunctionRef, GenericFunctionRef, SyntaxLevel};
use syntax::structure::Modifier;
use syntax::structure::traits::{Function, Terminator};
use syntax::structure::visitor::Translate;
use syntax::util::CompileError;
use syntax::util::translation::{translate_iterable, Translatable};
use crate::monomorphization::MonomorphizationContext;

/// A function in the MIR.
#[derive(Serialize, Deserialize, Clone)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
pub struct MediumFunction<T: SyntaxLevel> {
    /// The function reference
    pub reference: T::FunctionReference,
    /// The modifiers of the function
    pub modifiers: Vec<Modifier>,
    /// The parameters of the function
    pub parameters: Vec<T::TypeReference>,
    /// The return type of the function
    pub return_type: Option<T::TypeReference>,
    /// The body of the function
    pub body: Vec<CodeBlock<T>>,
}

impl<T: SyntaxLevel> Function<T::FunctionReference> for MediumFunction<T> {
    fn reference(&self) -> &T::FunctionReference {
        &self.reference
    }
}

impl<'a> Translate<(), MirFunctionContext<'a>> for HighFunction<HighSyntaxLevel> {
    fn translate(
        &self,
        context: &mut MirFunctionContext<'a>,
    ) -> Result<(), CompileError> {
        // Only translate non-generic functions.
        if !self.generics.is_empty() {
            return Ok(());
        }

        // Register function parameters as local variables and generate StorageLive statements
        for (param_name, param_type) in &self.parameters {
            let type_ref = HighSyntaxLevel::translate_type_ref(param_type, context)?;
            let local_var = context.get_or_create_local(*param_name, type_ref.clone());
            context.push_statement(crate::statement::MediumStatement::StorageLive(local_var, type_ref));
        }

        for statement in &self.body.statements {
            HighSyntaxLevel::translate_stmt(statement, context)?;
        }

        // Process the function body terminator if it's not None
        if self.body.terminator.is_none() {
            // Return void if we have no return at the very end
            if let MediumTerminator::Unreachable = context.code_blocks[context.current_block].terminator {
                context.set_terminator(MediumTerminator::Return(None));
            }
        } else {
            let terminator = HighSyntaxLevel::translate_terminator(&self.body.terminator, context)?;
            context.set_terminator(terminator);
        }

        let function = MediumFunction::<MediumSyntaxLevel> {
            reference: HighSyntaxLevel::translate_func_ref(&self.reference, context)?,
            modifiers: self.modifiers.clone(),
            body: mem::take(&mut context.code_blocks),
            parameters: self
                .parameters
                .iter()
                .map(|(_, ty)| Ok::<_, CompileError>(HighSyntaxLevel::translate_type_ref(ty, context)?))
                .collect::<Result<_, _>>()?,
            return_type: self
                .return_type
                .as_ref()
                .map(|ty| HighSyntaxLevel::translate_type_ref(ty, context))
                .transpose()?,
        };

        context.output.functions.insert(function.reference.clone(), function);
        Ok(())
    }
}


impl<'a> Translate<FunctionRef, MirFunctionContext<'a>> for GenericFunctionRef {
    fn translate(&self, context: &mut MirFunctionContext<'a>) -> Result<FunctionRef, CompileError> {
        if self.generics.is_empty() {
            return Ok(self.reference.clone());
        }

        Translate::<FunctionRef, MonomorphizationContext>::
        translate(&context.source.syntax.functions[self], &mut MonomorphizationContext {
            generics: translate_iterable(&self.generics, context,
                                         |generic, context|
                                             Ok((generic.clone(), Translate::translate(generic, context)?)))?,
            context,
        })
    }
}
