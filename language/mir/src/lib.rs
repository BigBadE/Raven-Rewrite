#![feature(let_chains)]

/// The MIR expression type and impls
pub mod expression;
/// The MIR function type and impls
pub mod function;
/// The MIR statement type and impls
pub mod statement;
/// The MIR type type and impls
pub mod types;
/// Pretty printing implementations for MIR types
pub mod pretty_print;
mod monomorphization;

use syntax::{FunctionRef, PrettyPrintableSyntaxLevel};
use std::fmt::Write;
use crate::expression::MediumExpression;
use crate::function::MediumFunction;
use crate::statement::MediumStatement;
use crate::types::MediumType;
use hir::expression::HighExpression;
use hir::function::{CodeBlock, HighFunction, HighTerminator};
use hir::statement::HighStatement;
use hir::types::{HighType, TypeData};
use hir::{HighSyntaxLevel, HirSource};
use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use syntax::structure::literal::Literal;
use syntax::structure::traits::Terminator;
use syntax::structure::visitor::Translate;
use syntax::util::translation::Translatable;
use syntax::util::{CompileError, Context};
use syntax::{ContextSyntaxLevel, GenericFunctionRef, Syntax, SyntaxLevel, GenericTypeRef, TypeRef};

/// The MIR level
#[derive(Serialize, Deserialize, Clone)]
pub struct MediumSyntaxLevel;

impl SyntaxLevel for MediumSyntaxLevel {
    type TypeReference = TypeRef;
    type Type = MediumType<MediumSyntaxLevel>;
    type FunctionReference = FunctionRef;
    type Function = MediumFunction<MediumSyntaxLevel>;
    type Statement = MediumStatement<MediumSyntaxLevel>;
    type Expression = MediumExpression<MediumSyntaxLevel>;
    type Terminator = MediumTerminator<MediumSyntaxLevel>;
}

impl<W: Write> PrettyPrintableSyntaxLevel<W> for MediumSyntaxLevel {}

impl ContextSyntaxLevel<HighSyntaxLevel> for MediumSyntaxLevel {
    type Context<'ctx> = MirContext<'ctx>;
    type InnerContext<'ctx> = MirFunctionContext<'ctx>;
}

/// A terminator for a MIR block
#[derive(Serialize, Deserialize, Clone)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
pub enum MediumTerminator<T: SyntaxLevel> {
    /// Goes to a specific block
    Goto(CodeBlockId),
    /// A goto that depends on a condition
    Switch {
        /// The condition to check
        discriminant: MediumExpression<T>,
        /// The blocks to jump to
        targets: Vec<(Literal, CodeBlockId)>,
        /// The fallback if none match
        fallback: CodeBlockId,
    },
    /// Returns a value
    Return(Option<T::Expression>),
    /// Should never be hit
    Unreachable,
}

/// An operand, a value that can be used in an expression
#[derive(Serialize, Deserialize, Clone)]
pub enum Operand {
    /// Copies the value at the place, like for a reference
    Copy(Place),
    /// Moves the value at the place
    Move(Place),
    /// A constant
    Constant(Literal),
}

impl Operand {
    /// Gets the type of the operand
    pub fn get_type(&self, context: &MirFunctionContext) -> TypeRef {
        match self {
            Operand::Copy(place) => context.translate(place),
            Operand::Move(place) => context.translate(place),
            Operand::Constant(literal) => literal.get_type(&context.source.syntax.symbols),
        }
    }
}

/// A location in memory that can be read from or written to
#[derive(Serialize, Deserialize, Clone)]
pub struct Place {
    /// Where this place is located
    pub local: LocalVar,
    /// The path to traverse to get to this place
    pub projection: Vec<PlaceElem>,
}

/// A way to traverse a place
#[derive(Serialize, Deserialize, Copy, Clone)]
pub enum PlaceElem {
    /// Dereferences a reference for the inner value
    Deref,
    /// Traverses to a field in a type
    Field(Spur),
    /// Indexes an array
    Index(usize),
}

/// A local variable
pub type LocalVar = usize;
/// A code block
pub type CodeBlockId = usize;

impl<T: SyntaxLevel> Terminator for MediumTerminator<T> {}

/// The context for parsing a HirSource into MIR
pub struct MirContext<'a> {
    /// The HIR source
    source: &'a HirSource,
    /// The MIR output
    output: Syntax<MediumSyntaxLevel>,
}

/// The context for compiling code to MIR. This flattens the syntax tree structure for code
/// into a control-flow graph. Since this means statements and expressions won't map one-to-one,
/// they are instead added to this structure.
pub struct MirFunctionContext<'a> {
    /// The blocks in the function
    code_blocks: Vec<CodeBlock<MediumSyntaxLevel>>,
    /// The block being written to
    current_block: usize,
    /// All current local variables
    local_vars: HashMap<Spur, LocalVar>,
    /// The variable types
    var_types: Vec<TypeRef>,
    /// The looping condition of the parent control block, if any
    parent_loop: Option<CodeBlockId>,
    /// The end of the parent control block, if any
    parent_end: Option<CodeBlockId>,
    /// The HIR source
    source: &'a HirSource,
    /// All generics in scope
    generics: HashMap<GenericTypeRef, TypeRef>,
    /// The output syntax
    output: &'a mut Syntax<MediumSyntaxLevel>,
}

impl<'a> MirContext<'a> {
    /// Creates a new MIR context
    fn new(source: &'a HirSource) -> Self {
        Self {
            source,
            output: Syntax {
                symbols: source.syntax.symbols.clone(),
                functions: HashMap::new(),
                types: HashMap::new(),
            },
        }
    }
}

impl<'a> MirFunctionContext<'a> {
    /// Creates a MIR function context
    fn new(source: &'a HirSource, output: &'a mut Syntax<MediumSyntaxLevel>) -> Self {
        Self {
            code_blocks: vec![CodeBlock {
                statements: vec![],
                terminator: MediumTerminator::Unreachable,
            }],
            current_block: 0,
            var_types: vec![],
            local_vars: HashMap::default(),
            parent_loop: None,
            parent_end: None,
            source,
            generics: HashMap::default(),
            output,
        }
    }

    /// Translates a place to its type
    pub fn translate(&self, place: &Place) -> TypeRef {
        let mut current_type = self.var_types[place.local].clone();
        for projection in &place.projection {
            match projection {
                PlaceElem::Field(field_name) => {
                    let generic_type_ref = GenericTypeRef::from(current_type.clone());
                    if let Some(struct_def) = self.source.syntax.types.get(&generic_type_ref) &&
                        let TypeData::Struct { fields } = &struct_def.data &&
                        let Some((_, field_type)) = fields.iter().find(|(name, _)| name == field_name) {
                        match field_type {
                            GenericTypeRef::Struct { reference, generics: _ } => {
                                current_type = reference.clone();
                            }
                            GenericTypeRef::Generic { reference } => {
                                current_type = reference.clone();
                            }
                        }
                    } else {
                        panic!("Error during field access translation!");
                    }
                }
                PlaceElem::Deref => {
                    // For dereference, we'd need to handle pointer/reference types
                    todo!("Dereference not implemented")
                }
                PlaceElem::Index(_) => {
                    // For indexing, we'd need to handle array types
                    todo!("Indexing not implemented")
                }
            }
        }
        current_type
    }

    /// Create a new basic block and return its ID
    pub fn create_block(&mut self) -> CodeBlockId {
        let id = self.code_blocks.len();
        self.code_blocks.push(CodeBlock {
            statements: Vec::new(),
            terminator: MediumTerminator::Unreachable, // Placeholder
        });
        id
    }

    /// Switch to a different block for emitting instructions
    pub fn switch_to_block(&mut self, block_id: CodeBlockId) {
        self.current_block = block_id;
    }

    /// Add a statement to the current block
    pub fn push_statement(&mut self, statement: MediumStatement<MediumSyntaxLevel>) {
        self.code_blocks[self.current_block]
            .statements
            .push(statement);
    }

    /// Set the terminator for the current block
    pub fn set_terminator(&mut self, terminator: MediumTerminator<MediumSyntaxLevel>) {
        self.code_blocks[self.current_block].terminator = terminator;
    }

    /// Create a new temporary variable
    pub fn create_temp(&mut self, type_ref: TypeRef) -> LocalVar {
        self.var_types.push(type_ref);
        self.var_types.len() - 1
    }

    /// Gets a local variable
    pub fn get_local(&mut self, name: Spur) -> Option<&LocalVar> {
        self.local_vars.get(&name)
    }

    /// Get or create a local variable for a named variable
    pub fn get_or_create_local(&mut self, name: Spur, types: TypeRef) -> LocalVar {
        if let Some(local) = self.local_vars.get(&name) {
            *local
        } else {
            self.local_vars.insert(name, self.var_types.len());
            self.var_types.push(types);
            self.var_types.len() - 1
        }
    }
}

impl Context<HighSyntaxLevel, MediumSyntaxLevel> for MirContext<'_> {
    fn function_context(&mut self, _function: &HighFunction<HighSyntaxLevel>) -> Result<MirFunctionContext<'_>, CompileError> {
        Ok(MirFunctionContext::new(self.source, &mut self.output))
    }

    fn type_context(&mut self, _types: &HighType<HighSyntaxLevel>) -> Result<MirFunctionContext<'_>, CompileError> {
        Ok(MirFunctionContext::new(self.source, &mut self.output))
    }
}

/// Resolves a HIR source to MIR
pub fn resolve_to_mir(source: HirSource) -> Result<Syntax<MediumSyntaxLevel>, CompileError> {
    let mut context = MirContext::new(&source);
    source.syntax.translate(&mut context)?;
    Ok(context.output)
}

impl Translatable<HighSyntaxLevel, MediumSyntaxLevel> for HighSyntaxLevel {
    fn translate_stmt(
        node: &HighStatement<HighSyntaxLevel>,
        context: &mut MirFunctionContext,
    ) -> Result<MediumStatement<MediumSyntaxLevel>, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_expr(
        node: &HighExpression<HighSyntaxLevel>,
        context: &mut MirFunctionContext,
    ) -> Result<MediumExpression<MediumSyntaxLevel>, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_type_ref(
        node: &GenericTypeRef,
        context: &mut MirFunctionContext,
    ) -> Result<TypeRef, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_func_ref(
        node: &GenericFunctionRef,
        context: &mut MirFunctionContext,
    ) -> Result<FunctionRef, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_type(
        node: &HighType<HighSyntaxLevel>,
        context: &mut MirFunctionContext,
    ) -> Result<(), CompileError> {
        Translate::translate(node, context)
    }

    fn translate_func(
        node: &HighFunction<HighSyntaxLevel>,
        context: &mut MirFunctionContext,
    ) -> Result<(), CompileError> {
        Translate::translate(node, context)
    }

    fn translate_terminator(
        node: &HighTerminator<HighSyntaxLevel>,
        context: &mut MirFunctionContext,
    ) -> Result<MediumTerminator<MediumSyntaxLevel>, CompileError> {
        Translate::translate(node, context)
    }
}

impl<'a>
Translate<MediumTerminator<MediumSyntaxLevel>, MirFunctionContext<'a>> for HighTerminator<HighSyntaxLevel>
{
    fn translate(
        &self,
        context: &mut MirFunctionContext<'a>,
    ) -> Result<MediumTerminator<MediumSyntaxLevel>, CompileError> {
        Ok(match self {
            HighTerminator::Return(returning) => MediumTerminator::Return(
                returning
                    .as_ref()
                    .map(|inner| HighSyntaxLevel::translate_expr(inner, context))
                    .transpose()?,
            ),
            HighTerminator::Break => {
                MediumTerminator::Goto(*context.parent_end.as_ref().ok_or(CompileError::Basic(
                    "Expected to be inside a control block to break from".to_string(),
                ))?)
            }
            HighTerminator::Continue => {
                MediumTerminator::Goto(*context.parent_loop.as_ref().ok_or(CompileError::Basic(
                    "Expected to be inside a control block to continue".to_string(),
                ))?)
            }
            HighTerminator::None => unreachable!(),
        })
    }
}
