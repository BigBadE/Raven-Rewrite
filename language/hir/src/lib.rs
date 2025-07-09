use crate::expression::HighExpression;
use crate::function::{CodeBlock, HighFunction, HighTerminator};
use crate::statement::HighStatement;
use crate::types::{HighType, TypeData};
use indexmap::IndexMap;
use lasso::{Spur, ThreadedRodeo};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use syntax::structure::literal::TYPES;
use syntax::structure::traits::{Function, FunctionReference, Type, TypeReference};
use syntax::structure::visitor::Translate;
use syntax::structure::Modifier;
use syntax::util::path::FilePath;
use syntax::util::translation::{translate_iterable, Translatable};
use syntax::util::{CompileError, Context};

use syntax::{ContextSyntaxLevel, GenericFunctionRef, GenericTypeRef, Syntax, SyntaxLevel};
use syntax::util::pretty_print::PrettyPrint;
use crate::pretty_print::format_generic_type_ref_with_generics_context;

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
    /// All the types by path
    pub types: HashMap<FilePath, GenericTypeRef>,
    /// All the functions by path
    pub functions: HashMap<FilePath, GenericFunctionRef>,
    /// All pre unary operations (like !true)
    pub pre_unary_operations: HashMap<Spur, Vec<GenericFunctionRef>>,
    /// All post unary operations (like foo?)
    pub post_unary_operations: HashMap<Spur, Vec<GenericFunctionRef>>,
    /// All binary operations (like 1 + 2)
    pub binary_operations: HashMap<Spur, Vec<GenericFunctionRef>>,
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
        functions: HashMap::default(),
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
    type FunctionReference = GenericFunctionRef;
    type Function = HighFunction<HighSyntaxLevel>;
    type Statement = HighStatement<HighSyntaxLevel>;
    type Expression = HighExpression<HighSyntaxLevel>;
    type Terminator = HighTerminator<HighSyntaxLevel>;
}

impl<I: SyntaxLevel<Type = HighType<I>, Function = HighFunction<I>> + Translatable<I, HighSyntaxLevel>>
    ContextSyntaxLevel<I> for HighSyntaxLevel
{
    type Context<'ctx> = HirContext<'ctx>;
    type InnerContext<'ctx> = HirFunctionContext<'ctx>;
}

/// A raw type reference, which hasn't been resolved yet.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
pub struct RawTypeRef {
    /// The path to the type
    pub path: FilePath,
    /// The generic constraints of the type
    pub generics: Vec<RawTypeRef>,
}

/// A raw function reference, which hasn't been resolved yet.
#[derive(Serialize, Deserialize, Debug, Clone, Eq, PartialEq, Hash)]
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
    pub pre_unary_operations: HashMap<Spur, Vec<GenericFunctionRef>>,
    /// Unary operations after the value (like foo?)
    pub post_unary_operations: HashMap<Spur, Vec<GenericFunctionRef>>,
    /// Binary operations (like 1 + 2)
    pub binary_operations: HashMap<Spur, Vec<GenericFunctionRef>>,
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
    pub func_cache: HashMap<Spur, GenericFunctionRef>,
    /// The currently in scope generics
    pub generics: IndexMap<Spur, Vec<GenericTypeRef>>,
    /// The currently being translated file
    pub file: FilePath,
}

impl<'a> HirFunctionContext<'a> {
    pub fn new<T: SyntaxLevel<Type=HighType<T>, Function=HighFunction<T>> + Translatable<T, HighSyntaxLevel>>(
        source: &'a RawSource,
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

        context.generics = translate_iterable(&generics, &mut context, |types, context| {
            translate_iterable(types, context, T::translate_type_ref)
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
        HirFunctionContext::new::<I>(self.source, function.reference().clone(), &function.generics)
    }

    fn type_context(&mut self, types: &I::Type) -> Result<HirFunctionContext<'_>, CompileError> {
        HirFunctionContext::new::<I>(self.source, types.reference().clone(), &types.generics)
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
                import.format(&context.source.syntax.symbols),
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
    ) -> Result<Vec<HighType<HighSyntaxLevel>>, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_func(
        node: &HighFunction<RawSyntaxLevel>,
        context: &mut HirFunctionContext<'_>,
    ) -> Result<Vec<HighFunction<HighSyntaxLevel>>, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_terminator(
        node: &HighTerminator<RawSyntaxLevel>,
        context: &mut HirFunctionContext<'_>,
    ) -> Result<HighTerminator<HighSyntaxLevel>, CompileError> {
        Translate::translate(node, context)
    }
}

/// Pretty printing implementations for HIR
impl HighFunction<HighSyntaxLevel> {
    pub fn generate_code(&self, syntax: &Syntax<HighSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        let mut code = String::new();

        // Add modifiers
        for modifier in &self.modifiers {
            match modifier {
                Modifier::PUBLIC => code.push_str("pub "),
                Modifier::OPERATION => code.push_str("operation "),
            }
        }

        code.push_str("fn ");
        code.push_str(&self.reference.format(interner));

        // Add generics
        if !self.generics.is_empty() {
            code.push('<');
            let generic_strs: Vec<String> = self.generics.keys()
                .map(|k| interner.resolve(k).to_string())
                .collect();
            code.push_str(&generic_strs.join(", "));
            code.push('>');
        }

        // Add parameters
        code.push('(');
        let param_strs: Vec<String> = self.parameters.iter()
            .map(|(name, type_ref)| {
                format!("{}: {}", interner.resolve(name), format_generic_type_ref_with_generics_context(type_ref, syntax, interner, &IndexMap::default()))
            })
            .collect();
        code.push_str(&param_strs.join(", "));
        code.push(')');

        // Add return type
        if let Some(return_type) = &self.return_type {
            code.push_str(" -> ");
            code.push_str(&format_generic_type_ref_with_generics_context(return_type, syntax, interner, &IndexMap::default()));
        }

        // Add body
        code.push_str(" {\n");
        code.push_str(&self.body.generate_code(syntax, interner, 1));
        code.push_str("}");

        code
    }
}

impl CodeBlock<HighSyntaxLevel> {
    pub fn generate_code(&self, syntax: &Syntax<HighSyntaxLevel>, interner: &ThreadedRodeo, indent_level: usize) -> String {
        let mut code = String::new();
        let indent = "    ".repeat(indent_level);

        // Generate statements
        for stmt in &self.statements {
            code.push_str(&stmt.generate_code(syntax, interner, indent_level));
            code.push('\n');
        }

        // Generate terminator
        code.push_str(&indent);
        code.push_str(&self.terminator.generate_code(syntax, interner));
        code.push('\n');

        code
    }
}

impl HighType<HighSyntaxLevel> {
    pub fn generate_code(&self, syntax: &Syntax<HighSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        let mut code = String::new();

        // Add modifiers
        for modifier in &self.modifiers {
            match modifier {
                Modifier::PUBLIC => code.push_str("pub "),
                Modifier::OPERATION => code.push_str("operation "),
            }
        }

        match &self.data {
            TypeData::Struct { fields } => {
                code.push_str("struct ");
                code.push_str(&self.reference.format(interner));

                // Add generics
                if !self.generics.is_empty() {
                    code.push('<');
                    let generic_strs: Vec<String> = self.generics.keys()
                        .map(|k| interner.resolve(k).to_string())
                        .collect();
                    code.push_str(&generic_strs.join(", "));
                    code.push('>');
                }

                code.push_str(" {\n");

                // Add fields
                for (field_name, field_type) in fields {
                    code.push_str(&format!("    {}: {},\n",
                        interner.resolve(field_name),
                        format_generic_type_ref_with_generics_context(field_type, syntax, interner, &IndexMap::default())
                    ));
                }

                code.push_str("}");
            },
            TypeData::Trait { functions } => {
                code.push_str("trait ");
                code.push_str(&self.reference.format(interner));

                // Add generics
                if !self.generics.is_empty() {
                    code.push('<');
                    let generic_strs: Vec<String> = self.generics.keys()
                        .map(|k| interner.resolve(k).to_string())
                        .collect();
                    code.push_str(&generic_strs.join(", "));
                    code.push('>');
                }

                code.push_str(" {\n");

                // Add function signatures
                for func in functions {
                    let func_code = func.generate_code(syntax, interner);
                    // Remove the body part for trait definitions
                    if let Some(body_start) = func_code.find(" {") {
                        code.push_str("    ");
                        code.push_str(&func_code[..body_start]);
                        code.push_str(";\n");
                    }
                }

                code.push_str("}");
            }
        }

        code
    }
}

/// Code generation for expressions
impl HighExpression<HighSyntaxLevel> {
    pub fn generate_code(&self, syntax: &Syntax<HighSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        match self {
            HighExpression::Literal(literal) => {
                // Use basic formatting for literals
                match literal {
                    syntax::structure::literal::Literal::String(spur) => format!("\"{}\"", interner.resolve(spur)),
                    syntax::structure::literal::Literal::F64(val) => format!("{}", val),
                    syntax::structure::literal::Literal::F32(val) => format!("{}f32", val),
                    syntax::structure::literal::Literal::I64(val) => format!("{}", val),
                    syntax::structure::literal::Literal::I32(val) => format!("{}i32", val),
                    syntax::structure::literal::Literal::U64(val) => format!("{}u64", val),
                    syntax::structure::literal::Literal::U32(val) => format!("{}u32", val),
                    syntax::structure::literal::Literal::Bool(val) => format!("{}", val),
                    syntax::structure::literal::Literal::Char(val) => format!("'{}'", val),
                }
            },
            HighExpression::Variable(name) => interner.resolve(name).to_string(),
            HighExpression::CodeBlock { body, value } => {
                let mut code = String::new();
                code.push_str("{\n");
                for stmt in body {
                    code.push_str("    ");
                    code.push_str(&stmt.generate_code(syntax, interner, 1));
                    code.push('\n');
                }
                code.push_str("    ");
                code.push_str(&value.generate_code(syntax, interner));
                code.push('\n');
                code.push_str("}");
                code
            },
            HighExpression::Assignment { declaration, variable, value } => {
                let mut code = String::new();
                if *declaration {
                    code.push_str("let ");
                }
                code.push_str(interner.resolve(variable));
                code.push_str(" = ");
                code.push_str(&value.generate_code(syntax, interner));
                code
            },
            HighExpression::FunctionCall { function, target, arguments } => {
                let mut code = String::new();
                if let Some(target) = target {
                    code.push_str(&target.generate_code(syntax, interner));
                    code.push('.');
                }
                // Format function reference
                code.push_str(&format!("func_{}", function.reference.format(interner)));
                if !function.generics.is_empty() {
                    code.push('<');
                    let generic_strs: Vec<String> = function.generics.iter()
                        .map(|g| format_generic_type_ref_with_generics_context(g, syntax, interner, &IndexMap::default()))
                        .collect();
                    code.push_str(&generic_strs.join(", "));
                    code.push('>');
                }
                code.push('(');
                let arg_strs: Vec<String> = arguments.iter()
                    .map(|arg| arg.generate_code(syntax, interner))
                    .collect();
                code.push_str(&arg_strs.join(", "));
                code.push(')');
                code
            },
            HighExpression::UnaryOperation { pre, symbol, value } => {
                let symbol_str = interner.resolve(symbol);
                if *pre {
                    format!("{}{}", symbol_str, value.generate_code(syntax, interner))
                } else {
                    format!("{}{}", value.generate_code(syntax, interner), symbol_str)
                }
            },
            HighExpression::BinaryOperation { symbol, first, second } => {
                format!("{} {} {}",
                    first.generate_code(syntax, interner),
                    interner.resolve(symbol),
                    second.generate_code(syntax, interner)
                )
            },
            HighExpression::CreateStruct { target_struct, fields } => {
                let mut code = String::new();
                // Format struct type reference
                match target_struct {
                    GenericTypeRef::Struct { reference, generics } => {
                        code.push_str(&format!("Type{}", reference));
                        if !generics.is_empty() {
                            code.push('<');
                            let generic_strs: Vec<String> = generics.iter()
                                .map(|g| match g {
                                    GenericTypeRef::Struct { reference, .. } => format!("Type{}", reference),
                                    GenericTypeRef::Generic { reference } => format!("T{}", reference),
                                })
                                .collect();
                            code.push_str(&generic_strs.join(", "));
                            code.push('>');
                        }
                    },
                    GenericTypeRef::Generic { reference } => {
                        code.push_str(&format!("T{}", reference));
                    }
                }
                code.push_str(" { ");
                let field_strs: Vec<String> = fields.iter()
                    .map(|(name, expr)| format!("{}: {}",
                        interner.resolve(name),
                        expr.generate_code(syntax, interner)
                    ))
                    .collect();
                code.push_str(&field_strs.join(", "));
                code.push_str(" }");
                code
            }
        }
    }
}

/// Code generation for statements
impl HighStatement<HighSyntaxLevel> {
    pub fn generate_code(&self, syntax: &Syntax<HighSyntaxLevel>, interner: &ThreadedRodeo, indent_level: usize) -> String {
        let indent = "    ".repeat(indent_level);
        match self {
            HighStatement::Expression(expr) => {
                format!("{}{};", indent, expr.generate_code(syntax, interner))
            },
            HighStatement::CodeBlock(statements) => {
                let mut code = format!("{}{{\n", indent);
                for stmt in statements {
                    code.push_str(&stmt.generate_code(syntax, interner, indent_level + 1));
                    code.push('\n');
                }
                code.push_str(&format!("{}}}", indent));
                code
            },
            HighStatement::Terminator(terminator) => {
                format!("{}{}", indent, terminator.generate_code(syntax, interner))
            },
            HighStatement::If { conditions, else_branch } => {
                let mut code = String::new();
                for (i, condition) in conditions.iter().enumerate() {
                    if i == 0 {
                        code.push_str(&format!("{}if {} {{\n", indent, condition.condition.generate_code(syntax, interner)));
                    } else {
                        code.push_str(&format!("{} else if {} {{\n", indent, condition.condition.generate_code(syntax, interner)));
                    }
                    for stmt in &condition.branch {
                        code.push_str(&stmt.generate_code(syntax, interner, indent_level + 1));
                        code.push('\n');
                    }
                    code.push_str(&format!("{}}}", indent));
                }
                if let Some(else_branch) = else_branch {
                    code.push_str(&format!(" else {{\n"));
                    for stmt in else_branch {
                        code.push_str(&stmt.generate_code(syntax, interner, indent_level + 1));
                        code.push('\n');
                    }
                    code.push_str(&format!("{}}}", indent));
                }
                code
            },
            HighStatement::For { condition } => {
                let mut code = format!("{}for {} {{\n", indent, condition.condition.generate_code(syntax, interner));
                for stmt in &condition.branch {
                    code.push_str(&stmt.generate_code(syntax, interner, indent_level + 1));
                    code.push('\n');
                }
                code.push_str(&format!("{}}}", indent));
                code
            },
            HighStatement::While { condition } => {
                let mut code = format!("{}while {} {{\n", indent, condition.condition.generate_code(syntax, interner));
                for stmt in &condition.branch {
                    code.push_str(&stmt.generate_code(syntax, interner, indent_level + 1));
                    code.push('\n');
                }
                code.push_str(&format!("{}}}", indent));
                code
            },
            HighStatement::Loop { body } => {
                let mut code = format!("{}loop {{\n", indent);
                for stmt in body {
                    code.push_str(&stmt.generate_code(syntax, interner, indent_level + 1));
                    code.push('\n');
                }
                code.push_str(&format!("{}}}", indent));
                code
            }
        }
    }
}

/// Code generation for terminators
impl HighTerminator<HighSyntaxLevel> {
    pub fn generate_code(&self, syntax: &Syntax<HighSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        match self {
            HighTerminator::Return(expr) => {
                if let Some(expr) = expr {
                    format!("return {}", expr.generate_code(syntax, interner))
                } else {
                    "return".to_string()
                }
            },
            HighTerminator::Break => "break".to_string(),
            HighTerminator::Continue => "continue".to_string(),
            HighTerminator::None => "".to_string(),
        }
    }
}




