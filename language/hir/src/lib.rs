use syntax::PrettyPrintableSyntaxLevel;
use std::fmt::Write;
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
use syntax::util::path::FilePath;
use syntax::util::translation::{translate_iterable, Translatable};
use syntax::util::{CompileError, Context};

use syntax::{ContextSyntaxLevel, GenericFunctionRef, GenericTypeRef, Syntax, SyntaxLevel};
use syntax::util::pretty_print::PrettyPrint;

/// The HIR expression type and impls
pub mod expression;
/// The HIR function type and impls
pub mod function;
/// The HIR statement type and impls
pub mod statement;
/// The HIR type type and impls
pub mod types;
/// Pretty printing implementations for HIR types
pub mod pretty_print;

/// A representation of the source code in its raw form. No linking or verifying has been done yet.
/// Contains some additional bookkeeping information, such as the operations.
pub struct RawSource {
    /// The syntax
    pub syntax: Syntax<RawSyntaxLevel>,
    /// Each file's imports
    pub imports: HashMap<FilePath, Vec<FilePath>>,
    /// All pre unary operations (like !true)
    pub pre_unary_operations: HashMap<Spur, Vec<GenericFunctionRef>>,
    /// All post unary operations (like foo?)
    pub post_unary_operations: HashMap<Spur, Vec<GenericFunctionRef>>,
    /// All binary operations (like 1 + 2)
    pub binary_operations: HashMap<Spur, Vec<GenericFunctionRef>>,
}

/// The raw syntax level, which is a one to one version of the source code.
#[derive(Serialize, Deserialize)]
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

impl<W: Write> PrettyPrintableSyntaxLevel<W> for RawSyntaxLevel {}

/// Creates a syntax with the internal types.
pub fn create_syntax() -> Syntax<RawSyntaxLevel> {
    let symbols = Arc::new(ThreadedRodeo::new());
    Syntax {
        functions: HashMap::default(),
        types: TYPES
            .iter()
            .map(|name| {
                let types = HighType::internal(symbols.get_or_intern(name));
                (types.reference.clone(), types)
            })
            .collect(),
        symbols,
    }
}

/// The high syntax level, which is the raw level with the types resolved.
#[derive(Serialize, Deserialize)]
pub struct HighSyntaxLevel;

impl SyntaxLevel for HighSyntaxLevel {
    type TypeReference = GenericTypeRef;
    type Type = HighType<HighSyntaxLevel>;
    type FunctionReference = GenericFunctionRef;
    type Function = HighFunction<HighSyntaxLevel>;
    type Statement = HighStatement<HighSyntaxLevel>;
    type Expression = HighExpression<HighSyntaxLevel>;
    type Terminator = HighTerminator<HighSyntaxLevel>;
}

impl<W: Write> PrettyPrintableSyntaxLevel<W> for HighSyntaxLevel {}

impl<I: SyntaxLevel<Type=HighType<I>, Function=HighFunction<I>> + Translatable<I, HighSyntaxLevel>>
ContextSyntaxLevel<I> for HighSyntaxLevel
{
    type Context<'ctx> = HirContext<'ctx>;
    type InnerContext<'ctx> = HirFunctionContext<'ctx>;
}

/// A raw type reference, which hasn't been resolved yet.
#[derive(Serialize, Deserialize, Clone, Eq, PartialEq, Hash)]
pub struct RawTypeRef {
    /// The path to the type
    pub path: FilePath,
    /// The generic constraints of the type
    pub generics: Vec<RawTypeRef>,
}

impl From<FilePath> for RawTypeRef {
    fn from(path: FilePath) -> Self {
        RawTypeRef {
            path,
            generics: Vec::new(),
        }
    }
}

/// A raw function reference, which hasn't been resolved yet.
#[derive(Serialize, Deserialize, Clone, Eq, PartialEq, Hash)]
pub struct RawFunctionRef {
    /// The path to the function
    pub path: FilePath,
    /// The generic constraints of the function
    pub generics: Vec<RawTypeRef>,
}

impl From<FilePath> for RawFunctionRef {
    fn from(path: FilePath) -> Self {
        RawFunctionRef {
            path,
            generics: vec![],
        }
    }
}

impl TypeReference for RawTypeRef {
    fn path(&self) -> FilePath {
        self.path.clone()
    }
}

impl FunctionReference for RawFunctionRef {
    fn path(&self) -> FilePath {
        self.path.clone()
    }
}

/// The HIR source code
pub struct HirSource {
    /// The syntax
    pub syntax: Syntax<HighSyntaxLevel>,
    /// Unary operations before the value (like !true)
    pub pre_unary_operations: HashMap<Spur, Vec<GenericFunctionRef>>,
    /// Unary operations after the value (like foo?)
    pub post_unary_operations: HashMap<Spur, Vec<GenericFunctionRef>>,
    /// Binary operations (like 1 + 2)
    pub binary_operations: HashMap<Spur, Vec<GenericFunctionRef>>,
}

/// Resolves a raw source into HIR
pub fn resolve_to_hir(source: RawSource) -> Result<HirSource, CompileError> {
    let mut context = HirContext { source: &source, output: Syntax {
        symbols: source.syntax.symbols.clone(),
        functions: HashMap::default(),
        types: HashMap::default(),
    } };

    source.syntax.translate(&mut context)?;

    Ok(HirSource {
        syntax: context.output,
        pre_unary_operations: source.pre_unary_operations,
        post_unary_operations: source.post_unary_operations,
        binary_operations: source.binary_operations,
    })
}

/// The context for HIR translation
pub struct HirContext<'a> {
    /// The raw source
    pub source: &'a RawSource,
    /// The output syntax
    pub output: Syntax<HighSyntaxLevel>,
}

/// The context for HIR function translation
pub struct HirFunctionContext<'a> {
    /// The raw source
    pub source: &'a RawSource,
    /// A cache for type lookups
    pub type_cache: HashMap<Spur, GenericTypeRef>,
    /// A cache for function lookups
    pub func_cache: HashMap<Spur, GenericFunctionRef>,
    /// The currently in scope generics
    pub generics: IndexMap<Spur, Vec<GenericTypeRef>>,
    /// The currently being translated file
    pub file: FilePath,
    /// The output syntax
    pub syntax: &'a mut Syntax<HighSyntaxLevel>,
}

impl<'a> HirFunctionContext<'a> {
    pub fn new<T: SyntaxLevel<Type = HighType<T>, Function = HighFunction<T>> + Translatable<T, HighSyntaxLevel>>(
        source: &'a RawSource,
        file: FilePath,
        generics: &IndexMap<Spur, Vec<T::TypeReference>>,
        syntax: &'a mut Syntax<HighSyntaxLevel>,
    ) -> Result<Self, CompileError> {
        let mut context = HirFunctionContext {
            source,
            type_cache: HashMap::default(),
            func_cache: HashMap::default(),
            generics: IndexMap::default(),
            file,
            syntax,
        };

        context.generics = translate_iterable(generics, &mut context, |(key, types), context| {
            Ok((*key, translate_iterable(types, context, T::translate_type_ref)?))
        })?;

        Ok(context)
    }
}

impl<
    I: SyntaxLevel<Type=HighType<I>, Function=HighFunction<I>> + Translatable<I, HighSyntaxLevel>,
> Context<I, HighSyntaxLevel> for HirContext<'_>
{
    fn function_context(
        &mut self,
        function: &I::Function,
    ) -> Result<HirFunctionContext<'_>, CompileError> {
        HirFunctionContext::new::<I>(self.source, function.reference().path(), &function.generics, &mut self.output)
    }

    fn type_context(&mut self, types: &I::Type) -> Result<HirFunctionContext<'_>, CompileError> {
        HirFunctionContext::new::<I>(self.source, types.reference().path(), &types.generics, &mut self.output)
    }
}

/// Handle reference translations
impl<'a> Translate<GenericTypeRef, HirFunctionContext<'a>> for RawTypeRef {
    fn translate(&self, context: &mut HirFunctionContext) -> Result<GenericTypeRef, CompileError> {
        if context.source.syntax.types.contains_key(&self.path.clone().into()) {
            return Ok(GenericTypeRef::Struct {
                reference: self.path.clone(),
                generics: translate_iterable(&self.generics, context, |ty, context| {
                    ty.translate(context)
                })?,
            });
        }

        if self.generics.is_empty()
            && self.path.len() == 1
            && context.generics.contains_key(&self.path[0])
        {
            return Ok(GenericTypeRef::Generic { reference: self.path.clone() });
        }

        for import in &context.source.imports[&context.file] {
            if import.last().unwrap() != self.path.first().unwrap() {
                continue;
            }
            if context.source.syntax.types.contains_key(&import.clone().into()) {
                return Ok(GenericTypeRef::Struct {
                    reference: self.path.clone(),
                    generics: translate_iterable(&self.generics, context, |ty, context| {
                        ty.translate(context)
                    })?,
                });
            }
            let mut failed = "Failed for ".to_string();
            import.format_top(&context.source.syntax.symbols, &mut failed)?;
            failed.push_str(":\n");
            for (key, value) in &context.source.syntax.types {
                key.format_top(&context.source.syntax.symbols, &mut failed)?;
                failed.push_str(": ");
                value.format_top(&context.source.syntax.symbols, &mut failed)?;
                failed.push('\n');
            }
        }

        todo!()
    }
}

impl<'a> Translate<GenericFunctionRef, HirFunctionContext<'a>> for RawFunctionRef {
    fn translate(
        &self,
        _context: &mut HirFunctionContext<'a>,
    ) -> Result<GenericFunctionRef, CompileError> {
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
    ) -> Result<GenericFunctionRef, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_type(
        node: &HighType<RawSyntaxLevel>,
        context: &mut HirFunctionContext<'_>,
    ) -> Result<(), CompileError> {
        Translate::translate(node, context)
    }

    fn translate_func(
        node: &HighFunction<RawSyntaxLevel>,
        context: &mut HirFunctionContext<'_>,
    ) -> Result<(), CompileError> {
        Translate::translate(node, context)
    }

    fn translate_terminator(
        node: &HighTerminator<RawSyntaxLevel>,
        context: &mut HirFunctionContext<'_>,
    ) -> Result<HighTerminator<HighSyntaxLevel>, CompileError> {
        Translate::translate(node, context)
    }
}