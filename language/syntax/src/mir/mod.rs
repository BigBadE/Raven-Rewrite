pub mod expression;
pub mod function;
pub mod statement;

use crate::hir::expression::HighExpression;
use crate::hir::function::HighFunction;
use crate::hir::statement::HighStatement;
use crate::hir::types::HighType;
use crate::hir::HighSyntaxLevel;
use crate::mir::expression::MediumExpression;
use crate::mir::function::MediumFunction;
use crate::mir::statement::MediumStatement;
use crate::structure::visitor::{FileOwner, Translate};
use crate::util::path::FilePath;
use crate::util::translation::Translatable;
use crate::util::ParseError;
use crate::{FunctionRef, Syntax, SyntaxLevel, TypeRef};

#[derive(Debug)]
pub struct MediumSyntaxLevel;

impl SyntaxLevel for MediumSyntaxLevel {
    type TypeReference = TypeRef;
    type Type = HighType<MediumSyntaxLevel>;
    type FunctionReference = FunctionRef;
    type Function = MediumFunction<MediumSyntaxLevel>;
    type Statement = MediumStatement<MediumSyntaxLevel>;
    type Expression = MediumExpression<MediumSyntaxLevel>;
}

pub struct MirContext {
    file: Option<FilePath>
}

impl FileOwner for MirContext {
    fn file(&self) -> &FilePath {
        self.file.as_ref().unwrap()
    }

    fn set_file(&mut self, file: FilePath) {
        self.file = Some(file);
    }
}

pub fn resolve_to_mir(source: Syntax<HighSyntaxLevel>) -> Result<Syntax<MediumSyntaxLevel>, ParseError> {
    source.translate(&mut MirContext {
        file: None
    })
}

impl Translatable<MirContext, HighSyntaxLevel, MediumSyntaxLevel> for MediumSyntaxLevel {
    fn translate_stmt(node: &HighStatement<HighSyntaxLevel>, context: &mut MirContext) -> Result<MediumStatement<MediumSyntaxLevel>, ParseError> {
        Translate::translate(node, context)
    }

    fn translate_expr(node: &HighExpression<HighSyntaxLevel>, context: &mut MirContext) -> Result<MediumExpression<MediumSyntaxLevel>, ParseError> {
        Translate::translate(node, context)
    }

    fn translate_type_ref(node: &TypeRef, context: &mut MirContext) -> Result<TypeRef, ParseError> {
        Translate::<_, _, HighSyntaxLevel, MediumSyntaxLevel>::translate(node, context)
    }

    fn translate_func_ref(node: &FunctionRef, context: &mut MirContext) -> Result<FunctionRef, ParseError> {
        Translate::<_, _, HighSyntaxLevel, MediumSyntaxLevel>::translate(node, context)
    }

    fn translate_type(node: &HighType<HighSyntaxLevel>, context: &mut MirContext) -> Result<HighType<MediumSyntaxLevel>, ParseError> {
        Translate::translate(node, context)
    }

    fn translate_func(node: &HighFunction<HighSyntaxLevel>, context: &mut MirContext) -> Result<MediumFunction<MediumSyntaxLevel>, ParseError> {
        Translate::translate(node, context)
    }
}