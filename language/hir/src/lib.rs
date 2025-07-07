use crate::expression::HighExpression;
use crate::function::{HighFunction, HighTerminator};
use crate::statement::HighStatement;
use crate::types::HighType;
use indexmap::IndexMap;
use lasso::{Spur, ThreadedRodeo};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use syntax::structure::literal::TYPES;
use syntax::structure::traits::{Function, FunctionReference, Type, TypeReference};
use syntax::structure::visitor::Translate;
use syntax::util::path::{FilePath, path_to_str};
use syntax::util::translation::{Translatable, translate_map, translate_vec};
use syntax::util::{CompileError, Context};
use syntax::{ContextSyntaxLevel, FunctionRef, GenericTypeRef, Syntax, SyntaxLevel};

/// The HIR expression type and impls
pub mod expression;
/// The HIR function type and impls
pub mod function;
/// The HIR statement type and impls
pub mod statement;
/// The HIR type type and impls
pub mod types;

/// A representation of the source code in its raw form. No linking or verifying has been done yet.
/// Contains some additional bookkeeping information, such as the operations.
pub struct RawSource {
    /// The syntax
    pub syntax: Syntax<RawSyntaxLevel>,
    /// Each file's imports
    pub imports: HashMap<FilePath, Vec<FilePath>>,
    /// All the types by path
    pub types: HashMap<FilePath, GenericTypeRef>,
    /// All the functions by path
    pub functions: HashMap<FilePath, FunctionRef>,
    /// All pre unary operations (like !true)
    pub pre_unary_operations: HashMap<Spur, Vec<FunctionRef>>,
    /// All post unary operations (like foo?)
    pub post_unary_operations: HashMap<Spur, Vec<FunctionRef>>,
    /// All binary operations (like 1 + 2)
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
    type TypeReference = GenericTypeRef;
    type Type = HighType<HighSyntaxLevel>;
    type FunctionReference = FunctionRef;
    type Function = HighFunction<HighSyntaxLevel>;
    type Statement = HighStatement<HighSyntaxLevel>;
    type Expression = HighExpression<HighSyntaxLevel>;
    type Terminator = HighTerminator<HighSyntaxLevel>;
}

impl<I: SyntaxLevel<Function = HighFunction<I>> + Translatable<I, HighSyntaxLevel>>
    ContextSyntaxLevel<I> for HighSyntaxLevel
{
    type Context<'ctx> = HirContext<'ctx>;
    type InnerContext<'ctx> = HirFunctionContext<'ctx>;
}

/// A raw type reference, which hasn't been resolved yet.
#[derive(Serialize, Deserialize, Clone, Debug)]
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
    let mut context = HirContext { source: &source };

    Ok(HirSource {
        syntax: source.syntax.translate(&mut context)?,
        pre_unary_operations: source.pre_unary_operations,
        post_unary_operations: source.post_unary_operations,
        binary_operations: source.binary_operations,
    })
}

/// The context for HIR translation
pub struct HirContext<'a> {
    /// The raw source
    pub source: &'a RawSource,
}

/// The context for HIR function translation
pub struct HirFunctionContext<'a> {
    /// The raw source
    pub source: &'a RawSource,
    /// A cache for type lookups
    pub type_cache: HashMap<Spur, GenericTypeRef>,
    /// A cache for function lookups
    pub func_cache: HashMap<Spur, FunctionRef>,
    /// The currently in scope generics
    pub generics: IndexMap<Spur, Vec<GenericTypeRef>>,
    /// The currently being translated file
    pub file: FilePath,
}

impl HirFunctionContext<'_> {
    pub fn new<T: SyntaxLevel + Translatable<T, HighSyntaxLevel>>(
        source: &RawSource,
        file: FilePath,
        generics: &IndexMap<Spur, Vec<T::TypeReference>>,
    ) -> Result<Self, CompileError> {
        let mut context = HirFunctionContext {
            source,
            type_cache: HashMap::default(),
            func_cache: HashMap::default(),
            generics: IndexMap::default(),
            file,
        };

        context.generics = translate_map(&generics, &mut context, |types, context| {
            translate_vec(types, context, T::translate_type_ref)
        })?;

        Ok(context)
    }
}

impl<
    I: SyntaxLevel<Type = HighType<I>, Function = HighFunction<I>> + Translatable<I, HighSyntaxLevel>,
> Context<I, HighSyntaxLevel> for HirContext<'_>
{
    fn function_context(
        &mut self,
        function: &I::Function,
    ) -> Result<HirFunctionContext<'_>, CompileError> {
        HirFunctionContext::new(self.source, function.file().clone(), &function.generics)
    }

    fn type_context(&mut self, types: &I::Type) -> Result<HirFunctionContext<'_>, CompileError> {
        HirFunctionContext::new(self.source, types.file().clone(), &types.generics)
    }
}

/// Handle reference translations
impl<'a> Translate<GenericTypeRef, HirFunctionContext<'a>> for RawTypeRef {
    fn translate(&self, context: &mut HirFunctionContext) -> Result<GenericTypeRef, CompileError> {
        if let Some(types) = context.source.types.get(&self.path) {
            return Ok(types.clone());
        }

        if self.generics.is_empty()
            && self.path.len() == 1
            && let Some(generic) = context.generics.get_index_of(&self.path[0])
        {
            return Ok(GenericTypeRef::Generic { reference: generic });
        }

        for import in &context.source.imports[&context.file] {
            if import.last().unwrap() != self.path.first().unwrap() {
                continue;
            }
            if let Some(types) = context.source.types.get(import) {
                return Ok(types.clone());
            }
            println!(
                "Failed for {:?}: {:?}",
                path_to_str(import, &context.source.syntax.symbols),
                context
                    .source
                    .types
                    .iter()
                    .map(|(key, value)| (path_to_str(key, &context.source.syntax.symbols), value))
                    .collect::<Vec<_>>()
            );
        }

        todo!()
    }
}

impl<'a> Translate<FunctionRef, HirFunctionContext<'a>> for RawFunctionRef {
    fn translate(
        &self,
        _context: &mut HirFunctionContext<'a>,
    ) -> Result<FunctionRef, CompileError> {
        todo!()
    }
}

impl Translatable<RawSyntaxLevel, HighSyntaxLevel> for RawSyntaxLevel {
    fn translate_stmt(
        node: &HighStatement<RawSyntaxLevel>,
        context: &mut HirFunctionContext<'_>,
    ) -> Result<HighStatement<HighSyntaxLevel>, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_expr(
        node: &HighExpression<RawSyntaxLevel>,
        context: &mut HirFunctionContext<'_>,
    ) -> Result<HighExpression<HighSyntaxLevel>, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_type_ref(
        node: &RawTypeRef,
        context: &mut HirFunctionContext<'_>,
    ) -> Result<GenericTypeRef, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_func_ref(
        node: &RawFunctionRef,
        context: &mut HirFunctionContext<'_>,
    ) -> Result<FunctionRef, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_type(
        node: &HighType<RawSyntaxLevel>,
        context: &mut HirFunctionContext<'_>,
    ) -> Result<Option<HighType<HighSyntaxLevel>>, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_func(
        node: &HighFunction<RawSyntaxLevel>,
        context: &mut HirFunctionContext<'_>,
    ) -> Result<HighFunction<HighSyntaxLevel>, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_terminator(
        node: &HighTerminator<RawSyntaxLevel>,
        context: &mut HirFunctionContext<'_>,
    ) -> Result<HighTerminator<HighSyntaxLevel>, CompileError> {
        Translate::translate(node, context)
    }
}
