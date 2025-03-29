use crate::expression::HighExpression;
use crate::function::{HighFunction, HighTerminator};
use crate::statement::HighStatement;
use crate::types::HighType;
use lasso::{Spur, ThreadedRodeo};
use std::collections::HashMap;
use std::sync::Arc;
use serde::{Deserialize, Serialize};
use syntax::structure::traits::{FunctionReference, TypeReference};
use syntax::util::path::FilePath;
use syntax::{FunctionRef, Syntax, SyntaxLevel, TypeRef};
use syntax::structure::FileOwner;
use syntax::structure::visitor::Translate;
use syntax::util::ParseError;
use syntax::util::translation::Translatable;

pub mod expression;
pub mod function;
pub mod statement;
pub mod types;

pub struct RawSource {
    pub syntax: Syntax<RawSyntaxLevel>,
    pub imports: HashMap<FilePath, Vec<FilePath>>,
    pub types: HashMap<FilePath, TypeRef>,
    pub functions: HashMap<FilePath, FunctionRef>,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct RawSyntaxLevel;

impl SyntaxLevel for RawSyntaxLevel {
    type TypeReference = RawTypeRef;
    type Type = HighType<RawSyntaxLevel>;
    type FunctionReference = RawFunctionRef;
    type Function = HighFunction<RawSyntaxLevel>;
    type Statement = HighStatement<RawSyntaxLevel>;
    type Expression = HighExpression<RawSyntaxLevel>;
    type Terminator = HighTerminator<RawSyntaxLevel>;
}

pub fn create_syntax() -> Syntax<RawSyntaxLevel> {
    let symbols = Arc::new(ThreadedRodeo::new());
    Syntax {
        functions: Vec::default(),
        types: vec![
            HighType::internal(symbols.get_or_intern("void")),
            HighType::internal(symbols.get_or_intern("str")),
            HighType::internal(symbols.get_or_intern("f64")),
            HighType::internal(symbols.get_or_intern("f32")),
            HighType::internal(symbols.get_or_intern("i64")),
            HighType::internal(symbols.get_or_intern("i32")),
            HighType::internal(symbols.get_or_intern("u64")),
            HighType::internal(symbols.get_or_intern("u32")),
            HighType::internal(symbols.get_or_intern("bool")),
            HighType::internal(symbols.get_or_intern("char")),
        ],
        symbols,
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct HighSyntaxLevel;

impl SyntaxLevel for HighSyntaxLevel {
    type TypeReference = TypeRef;
    type Type = HighType<HighSyntaxLevel>;
    type FunctionReference = FunctionRef;
    type Function = HighFunction<HighSyntaxLevel>;
    type Statement = HighStatement<HighSyntaxLevel>;
    type Expression = HighExpression<HighSyntaxLevel>;
    type Terminator = HighTerminator<HighSyntaxLevel>;
}

#[derive(Serialize, Deserialize, Debug)]
pub struct RawTypeRef(pub Spur);
#[derive(Serialize, Deserialize, Debug)]
pub struct RawFunctionRef(pub Spur);

impl TypeReference for RawTypeRef {}
impl FunctionReference for RawFunctionRef {}

pub fn resolve_to_hir(source: RawSource) -> Result<Syntax<HighSyntaxLevel>, ParseError> {
    let internal = |name, id| (source.syntax.symbols.get_or_intern(name), TypeRef(id));
    source.syntax.translate(&mut HirContext {
        file: None,
        imports: &source.imports,
        types: &source.types,
        type_cache: HashMap::default(),
        func_cache: HashMap::default(),
        internals: HashMap::from([
            internal("str", 1),
            internal("f64", 2),
            internal("f32", 3),
            internal("i64", 4),
            internal("i32", 5),
            internal("u64", 6),
            internal("u32", 7),
            internal("bool", 8),
            internal("char", 9),
        ]),
    })
}

pub struct HirContext<'a> {
    pub file: Option<FilePath>,
    pub imports: &'a HashMap<FilePath, Vec<FilePath>>,
    pub types: &'a HashMap<FilePath, TypeRef>,
    pub type_cache: HashMap<Spur, TypeRef>,
    pub func_cache: HashMap<Spur, FunctionRef>,
    pub internals: HashMap<Spur, TypeRef>,
}

impl<'a> FileOwner for HirContext<'a> {
    fn file(&self) -> &FilePath {
        self.file.as_ref().unwrap()
    }

    fn set_file(&mut self, file: FilePath) {
        self.file = Some(file);
    }
}

// Handle reference translations
impl<'a, I: SyntaxLevel, O: SyntaxLevel> Translate<TypeRef, HirContext<'a>, I, O> for RawTypeRef {
    fn translate(&self, context: &mut HirContext) -> Result<TypeRef, ParseError> {
        if let Some(internal) = context.internals.get(&self.0) {
            return Ok(*internal);
        }

        for import in &context.imports[context.file.as_ref().unwrap()] {
            if import.last().unwrap() == &self.0 {
                if let Some(types) = context.types.get(import) {
                    return Ok(*types);
                }
            }
        }
        todo!()
    }
}

impl<'a, I: SyntaxLevel, O: SyntaxLevel> Translate<FunctionRef, HirContext<'a>, I, O>
    for RawFunctionRef
{
    fn translate(&self, _context: &mut HirContext) -> Result<FunctionRef, ParseError> {
        todo!()
    }
}

impl<'a> Translatable<HirContext<'a>, RawSyntaxLevel, HighSyntaxLevel> for RawSyntaxLevel {
    fn translate_stmt(
        node: &HighStatement<RawSyntaxLevel>,
        context: &mut HirContext,
    ) -> Result<HighStatement<HighSyntaxLevel>, ParseError> {
        Translate::translate(node, context)
    }

    fn translate_expr(
        node: &HighExpression<RawSyntaxLevel>,
        context: &mut HirContext,
    ) -> Result<HighExpression<HighSyntaxLevel>, ParseError> {
        Translate::translate(node, context)
    }

    fn translate_type_ref(
        node: &RawTypeRef,
        context: &mut HirContext,
    ) -> Result<TypeRef, ParseError> {
        Translate::<_, _, RawSyntaxLevel, HighSyntaxLevel>::translate(node, context)
    }

    fn translate_func_ref(
        node: &RawFunctionRef,
        context: &mut HirContext,
    ) -> Result<FunctionRef, ParseError> {
        Translate::<_, _, RawSyntaxLevel, HighSyntaxLevel>::translate(node, context)
    }

    fn translate_type(
        node: &HighType<RawSyntaxLevel>,
        context: &mut HirContext,
    ) -> Result<HighType<HighSyntaxLevel>, ParseError> {
        Translate::translate(node, context)
    }

    fn translate_func(
        node: &HighFunction<RawSyntaxLevel>,
        context: &mut HirContext,
    ) -> Result<HighFunction<HighSyntaxLevel>, ParseError> {
        Translate::translate(node, context)
    }

    fn translate_terminator(
        node: &HighTerminator<RawSyntaxLevel>,
        context: &mut HirContext<'a>,
    ) -> Result<HighTerminator<HighSyntaxLevel>, ParseError> {
        Translate::translate(node, context)
    }
}
