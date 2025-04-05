use crate::expression::HighExpression;
use crate::function::{HighFunction, HighTerminator};
use crate::statement::HighStatement;
use crate::types::HighType;
use lasso::{Spur, ThreadedRodeo};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use syntax::structure::literal::TYPES;
use syntax::structure::traits::{FunctionReference, TypeReference};
use syntax::structure::visitor::Translate;
use syntax::structure::FileOwner;
use syntax::util::path::{path_to_str, FilePath};
use syntax::util::translation::Translatable;
use syntax::util::ParseError;
use syntax::{FunctionRef, Syntax, SyntaxLevel, TypeRef};

pub mod expression;
pub mod function;
pub mod statement;
pub mod types;

/// A representation of the source code in its raw form. No linking or verifying has been done yet.
/// Contains some additional bookkeeping information, such as the operations.
pub struct RawSource {
    pub syntax: Syntax<RawSyntaxLevel>,
    pub imports: HashMap<FilePath, Vec<FilePath>>,
    pub types: HashMap<FilePath, TypeRef>,
    pub functions: HashMap<FilePath, FunctionRef>,
    pub pre_unary_operations: HashMap<Spur, Vec<FunctionRef>>,
    pub post_unary_operations: HashMap<Spur, Vec<FunctionRef>>,
    pub binary_operations: HashMap<Spur, Vec<FunctionRef>>,
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
pub struct RawTypeRef(pub FilePath);
#[derive(Serialize, Deserialize, Debug)]
pub struct RawFunctionRef(pub FilePath);

impl TypeReference for RawTypeRef {}
impl FunctionReference for RawFunctionRef {}

pub struct HirSource {
    pub syntax: Syntax<HighSyntaxLevel>,
    pub pre_unary_operations: HashMap<Spur, Vec<FunctionRef>>,
    pub post_unary_operations: HashMap<Spur, Vec<FunctionRef>>,
    pub binary_operations: HashMap<Spur, Vec<FunctionRef>>,
}

pub fn resolve_to_hir(source: RawSource) -> Result<HirSource, ParseError> {
    let mut context = HirContext {
        file: None,
        symbols: source.syntax.symbols.clone(),
        imports: source.imports,
        types: source.types,
        type_cache: HashMap::default(),
        func_cache: HashMap::default(),
    };
    context.types.extend(TYPES
        .iter()
        .enumerate()
        .map(|(id, name)| (vec![source.syntax.symbols.get_or_intern(name)], TypeRef(id))));
    Ok(HirSource {
        syntax: source.syntax.translate(&mut context)?,
        pre_unary_operations: source.pre_unary_operations,
        post_unary_operations: source.post_unary_operations,
        binary_operations: source.binary_operations
    })
}

pub struct HirContext {
    pub file: Option<FilePath>,
    pub symbols: Arc<ThreadedRodeo>,
    pub imports: HashMap<FilePath, Vec<FilePath>>,
    pub types: HashMap<FilePath, TypeRef>,
    pub type_cache: HashMap<Spur, TypeRef>,
    pub func_cache: HashMap<Spur, FunctionRef>,
}

impl FileOwner for HirContext {
    fn file(&self) -> &FilePath {
        self.file.as_ref().unwrap()
    }

    fn set_file(&mut self, file: FilePath) {
        self.file = Some(file);
    }
}

// Handle reference translations
impl<'a, I: SyntaxLevel, O: SyntaxLevel> Translate<TypeRef, HirContext, I, O> for RawTypeRef {
    fn translate(&self, context: &mut HirContext) -> Result<TypeRef, ParseError> {
        if let Some(types) = context.types.get(&self.0) {
            return Ok(*types);
        }

        for import in &context.imports[context.file.as_ref().unwrap()] {
            if import.last().unwrap() == self.0.first().unwrap() {
                if let Some(types) = context.types.get(import) {
                    return Ok(*types);
                } else {
                    println!("Failed for {:?}: {:?}", path_to_str(import, &context.symbols),
                             context.types.iter().map(|(key, value)| (path_to_str(key, &context.symbols), value)).collect::<Vec<_>>());
                }
            }
        }

        todo!()
    }
}

impl<'a, I: SyntaxLevel, O: SyntaxLevel> Translate<FunctionRef, HirContext, I, O>
    for RawFunctionRef
{
    fn translate(&self, _context: &mut HirContext) -> Result<FunctionRef, ParseError> {
        todo!()
    }
}

impl<'a> Translatable<HirContext, RawSyntaxLevel, HighSyntaxLevel> for RawSyntaxLevel {
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
    ) -> Result<Option<HighType<HighSyntaxLevel>>, ParseError> {
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
        context: &mut HirContext,
    ) -> Result<HighTerminator<HighSyntaxLevel>, ParseError> {
        Translate::translate(node, context)
    }
}
