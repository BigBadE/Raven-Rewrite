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
use syntax::util::CompileError;
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

/// The raw syntax level, which is a one to one version of the source code.
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

/// Creates a syntax with the internal types.
pub fn create_syntax() -> Syntax<RawSyntaxLevel> {
    let symbols = Arc::new(ThreadedRodeo::new());
    Syntax {
        functions: Vec::default(),
        types: TYPES
            .iter()
            .map(|name| HighType::internal(symbols.get_or_intern(name)))
            .collect(),
        symbols,
    }
}

/// The high syntax level, which is the raw level with the types resolved.
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

/// A raw type reference, which hasn't been resolved yet.
#[derive(Serialize, Deserialize, Debug)]
pub struct RawTypeRef {
    /// The path to the type
    pub path: FilePath,
    /// The generic constraints of the type
    pub generics: Vec<RawTypeRef>,
}

/// A raw function reference, which hasn't been resolved yet.
#[derive(Serialize, Deserialize, Debug)]
pub struct RawFunctionRef {
    /// The path to the function
    pub path: FilePath,
    /// The generic constraints of the function
    pub generics: Vec<RawTypeRef>,
}

impl TypeReference for RawTypeRef {}
impl FunctionReference for RawFunctionRef {}

/// The HIR source code
pub struct HirSource {
    /// The syntax
    pub syntax: Syntax<HighSyntaxLevel>,
    /// Unary operations before the value (like !true)
    pub pre_unary_operations: HashMap<Spur, Vec<FunctionRef>>,
    /// Unary operations after the value (like foo?)
    pub post_unary_operations: HashMap<Spur, Vec<FunctionRef>>,
    /// Binary operations (like 1 + 2)
    pub binary_operations: HashMap<Spur, Vec<FunctionRef>>,
}

/// Resolves a raw source into HIR
pub fn resolve_to_hir(source: RawSource) -> Result<HirSource, CompileError> {
    let mut context = HirContext {
        file: None,
        symbols: source.syntax.symbols.clone(),
        imports: source.imports,
        types: source.types,
        type_cache: HashMap::default(),
        func_cache: HashMap::default(),
    };
    context.types.extend(
        TYPES
            .iter()
            .enumerate()
            .map(|(id, name)| (vec![source.syntax.symbols.get_or_intern(name)], TypeRef(id))),
    );

    Ok(HirSource {
        syntax: source.syntax.translate(&mut context)?,
        pre_unary_operations: source.pre_unary_operations,
        post_unary_operations: source.post_unary_operations,
        binary_operations: source.binary_operations,
    })
}

/// The context for HIR translation
pub struct HirContext {
    /// The currently being translated file
    pub file: Option<FilePath>,
    /// The symbols table
    pub symbols: Arc<ThreadedRodeo>,
    /// The current file's imports
    pub imports: HashMap<FilePath, Vec<FilePath>>,
    /// All types in the syntax
    pub types: HashMap<FilePath, TypeRef>,
    /// A cache for type lookups
    pub type_cache: HashMap<Spur, TypeRef>,
    /// A cache for function lookups
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

/// Handle reference translations
impl Translate<TypeRef, HirContext> for RawTypeRef {
    fn translate(&self, context: &mut HirContext) -> Result<TypeRef, CompileError> {
        if let Some(types) = context.types.get(&self.path) {
            return Ok(*types);
        }

        for import in &context.imports[context.file.as_ref().unwrap()] {
            if import.last().unwrap() == self.path.first().unwrap() {
                if let Some(types) = context.types.get(import) {
                    return Ok(*types);
                } else {
                    println!(
                        "Failed for {:?}: {:?}",
                        path_to_str(import, &context.symbols),
                        context
                            .types
                            .iter()
                            .map(|(key, value)| (path_to_str(key, &context.symbols), value))
                            .collect::<Vec<_>>()
                    );
                }
            }
        }

        todo!()
    }
}

impl Translate<FunctionRef, HirContext> for RawFunctionRef {
    fn translate(&self, _context: &mut HirContext) -> Result<FunctionRef, CompileError> {
        todo!()
    }
}

impl Translatable<HirContext, RawSyntaxLevel, HighSyntaxLevel> for RawSyntaxLevel {
    fn translate_stmt(
        node: &HighStatement<RawSyntaxLevel>,
        context: &mut HirContext,
    ) -> Result<HighStatement<HighSyntaxLevel>, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_expr(
        node: &HighExpression<RawSyntaxLevel>,
        context: &mut HirContext,
    ) -> Result<HighExpression<HighSyntaxLevel>, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_type_ref(
        node: &RawTypeRef,
        context: &mut HirContext,
    ) -> Result<TypeRef, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_func_ref(
        node: &RawFunctionRef,
        context: &mut HirContext,
    ) -> Result<FunctionRef, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_type(
        node: &HighType<RawSyntaxLevel>,
        context: &mut HirContext,
    ) -> Result<Option<HighType<HighSyntaxLevel>>, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_func(
        node: &HighFunction<RawSyntaxLevel>,
        context: &mut HirContext,
    ) -> Result<HighFunction<HighSyntaxLevel>, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_terminator(
        node: &HighTerminator<RawSyntaxLevel>,
        context: &mut HirContext,
    ) -> Result<HighTerminator<HighSyntaxLevel>, CompileError> {
        Translate::translate(node, context)
    }
}
