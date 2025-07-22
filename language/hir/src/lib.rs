use syntax::PrettyPrintableSyntaxLevel;
use std::fmt::Write;
use crate::expression::HighExpression;
use crate::function::{HighFunction, HighTerminator};
use crate::statement::HighStatement;
use crate::types::HighType;
use crate::impl_block::HighImpl;
use indexmap::IndexMap;
use lasso::{Spur, ThreadedRodeo};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use syntax::structure::literal::TYPES;
use syntax::structure::traits::{FunctionReference, TypeReference};
use syntax::structure::visitor::Translate;
use syntax::util::path::{get_file_path, FilePath};
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
/// The HIR impl block type and impls
pub mod impl_block;
/// Pretty printing implementations for HIR types
pub mod pretty_print;

/// A representation of the source code in its raw form. No linking or verifying has been done yet.
/// Contains some additional bookkeeping information, such as the operations.
pub struct RawSource {
    /// The syntax
    pub syntax: Syntax<RawSyntaxLevel>,
    /// Each file's imports
    pub imports: HashMap<FilePath, Vec<FilePath>>,
    /// All impl blocks
    pub impls: Vec<HighImpl<RawSyntaxLevel>>,
    /// All pre unary operations (like !true)
    pub pre_unary_operations: HashMap<Spur, Vec<GenericFunctionRef>>,
    /// All post unary operations (like foo?)
    pub post_unary_operations: HashMap<Spur, Vec<GenericFunctionRef>>,
    /// All binary operations (like 1 + 2)
    pub binary_operations: HashMap<Spur, Vec<GenericFunctionRef>>,
}

/// The raw syntax level, which is a one to one version of the source code.
#[derive(Serialize, Deserialize, Clone)]
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
#[derive(Serialize, Deserialize, Clone)]
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
    /// All impl blocks
    pub impls: Vec<HighImpl<HighSyntaxLevel>>,
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

    // Translate impl blocks FIRST, so their functions are available during main syntax translation
    let mut translated_impls = Vec::new();
    for impl_block in &source.impls {
        // Try to find the file where the target type is defined
        let target_type_name = &impl_block.target_type.path()[0];
        let impl_file = source.syntax.types.iter()
            .find(|(type_ref, _)| type_ref.path().last() == Some(target_type_name))
            .map(|(type_ref, _)| get_file_path(type_ref.path()))
            .or_else(|| source.imports.keys().next().cloned())
            .unwrap_or_else(|| vec![source.syntax.symbols.get_or_intern("main")]);
            
        let mut function_context = HirFunctionContext::new::<RawSyntaxLevel>(
            &source,
            impl_file,
            &impl_block.generics,
            &mut context.output,
        )?;
        impl_block.translate(&mut function_context)?;
        translated_impls.push(HighImpl {
            target_type: RawSyntaxLevel::translate_type_ref(&impl_block.target_type, &mut function_context)?,
            generics: impl_block
                .generics
                .iter()
                .map(|(name, generics)| {
                    Ok::<_, CompileError>((
                        name.clone(),
                        translate_iterable(generics, &mut function_context, RawSyntaxLevel::translate_type_ref)?,
                    ))
                })
                .collect::<Result<IndexMap<_, _>, _>>()?,
            modifiers: impl_block.modifiers.clone(),
            functions: Vec::new(), // Functions are already added to syntax by translate
        });
    }

    source.syntax.translate(&mut context)?;

    Ok(HirSource {
        syntax: context.output,
        impls: translated_impls,
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
        HirFunctionContext::new::<I>(self.source, get_file_path(function.reference.path()), &function.generics, &mut self.output)
    }

    fn type_context(&mut self, types: &I::Type) -> Result<HirFunctionContext<'_>, CompileError> {
        HirFunctionContext::new::<I>(self.source, get_file_path(types.reference.path()), &types.generics, &mut self.output)
    }
}

/// Handle reference translations
impl<'a> Translate<GenericTypeRef, HirFunctionContext<'a>> for RawTypeRef {
    fn translate(&self, context: &mut HirFunctionContext) -> Result<GenericTypeRef, CompileError> {
        resolve_type_reference(self, context)
    }
}

impl<'a> Translate<GenericFunctionRef, HirFunctionContext<'a>> for RawFunctionRef {
    fn translate(
        &self,
        context: &mut HirFunctionContext<'a>,
    ) -> Result<GenericFunctionRef, CompileError> {
        resolve_function_reference(self, context)
    }
}

fn check_imports<F: Fn(FilePath, &mut HirFunctionContext) -> Result<T, CompileError>, T>(
    context: &mut HirFunctionContext, path: &FilePath, types: bool, creator: F) -> Result<Option<T>, CompileError> {
    let mut current = context.file.clone();
    current.append(&mut path.clone());
    let target = |key: &FilePath| if types {
        context.source.syntax.types.contains_key(&key.clone().into())
    } else {
        context.source.syntax.functions.contains_key(&key.clone().into())
    };
    if target(&current) {
        return Ok(Some(creator(current, context)?));
    }

    if let Some(imports) = context.source.imports.get(&context.file) {
        
        for import in imports {
            if import.last().unwrap() != path.first().unwrap() {
                continue;
            }
            if target(&import) {
                let mut reference = import.clone();
                reference.append(&mut path.iter().cloned().skip(1).collect());
                return Ok(Some(creator(reference, context)?));
            }
        }
    }

    Ok(None)
}

/// Common resolution logic for both types and functions
enum ReferenceKind {
    Type,
    Function,
}

/// Shared resolution logic that both type and function references can use
fn resolve_reference_common(
    path: &FilePath,
    context: &mut HirFunctionContext,
    kind: ReferenceKind,
) -> Result<Option<FilePath>, CompileError> {
    let is_type = matches!(kind, ReferenceKind::Type);
    
    // Check if it exists directly in syntax
    let syntax_check = if is_type {
        context.source.syntax.types.contains_key(&path.clone().into())
    } else {
        context.source.syntax.functions.contains_key(&path.clone().into())
    };
    
    if syntax_check {
        return Ok(Some(path.clone()));
    }

    // For single-component paths, handle same-file resolution
    if path.len() == 1 {
        let name = &path[0];
        
        // Look for same-file resolution
        let mut same_file_path = context.file.clone();
        same_file_path.push(*name);
        
        let same_file_check = if is_type {
            context.source.syntax.types.contains_key(&same_file_path.clone().into())
        } else {
            context.source.syntax.functions.contains_key(&same_file_path.clone().into())
        };
        
        if same_file_check {
            return Ok(Some(same_file_path));
        }
        
        // For functions only: Check if any function in syntax.functions has this name as its last component (for method calls)
        if !is_type {
            for (func_ref, _) in &context.syntax.functions {
                if func_ref.path().last() == Some(name) {
                    return Ok(Some(func_ref.path()));
                }
            }
        }
    }

    // Check imports
    let import_result = check_imports(context, path, is_type, |import_path, _ctx| {
        Ok(import_path)
    })?;
    
    if let Some(import_path) = import_result {
        return Ok(Some(import_path));
    }

    Ok(None)
}

/// Resolve type reference using shared logic
fn resolve_type_reference(
    raw_ref: &RawTypeRef,
    context: &mut HirFunctionContext,
) -> Result<GenericTypeRef, CompileError> {
    // Check for generic parameters first (specific to types)
    if raw_ref.generics.is_empty()
        && raw_ref.path.len() == 1
        && context.generics.contains_key(&raw_ref.path[0])
    {
        return Ok(GenericTypeRef::Generic { reference: raw_ref.path.clone() });
    }

    // Use common resolution logic
    if let Some(resolved_path) = resolve_reference_common(&raw_ref.path, context, ReferenceKind::Type)? {
        return Ok(GenericTypeRef::Struct {
            reference: resolved_path,
            generics: translate_iterable(&raw_ref.generics, context, |ty, context| {
                ty.translate(context)
            })?,
        });
    }

    // Type resolution fails with error
    Err(CompileError::Basic(format!(
        "Failed to resolve type reference {} in file {}",
        raw_ref.path().format_top(&context.source.syntax.symbols, String::new())?,
        context.file.format_top(&context.source.syntax.symbols, String::new())?
    )))
}

/// Resolve function reference using shared logic
fn resolve_function_reference(
    raw_ref: &RawFunctionRef,
    context: &mut HirFunctionContext,
) -> Result<GenericFunctionRef, CompileError> {
    // Use common resolution logic
    if let Some(resolved_path) = resolve_reference_common(&raw_ref.path, context, ReferenceKind::Function)? {
        return Ok(GenericFunctionRef {
            reference: resolved_path,
            generics: translate_iterable(&raw_ref.generics, context, |ty, context| {
                ty.translate(context)
            })?,
        });
    }

    // Function resolution allows pass-through for later resolution
    Ok(GenericFunctionRef {
        reference: raw_ref.path.clone(),
        generics: translate_iterable(&raw_ref.generics, context, |ty, context| {
            ty.translate(context)
        })?,
    })
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