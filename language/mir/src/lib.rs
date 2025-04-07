/// The MIR expression type and impls
pub mod expression;
/// The MIR function type and impls
pub mod function;
/// The MIR statement type and impls
pub mod statement;
/// The MIR type type and impls
pub mod types;

use crate::expression::MediumExpression;
use crate::function::MediumFunction;
use crate::statement::MediumStatement;
use crate::types::MediumType;
use hir::expression::HighExpression;
use hir::function::{CodeBlock, HighFunction, HighTerminator};
use hir::statement::HighStatement;
use hir::types::HighType;
use hir::{HighSyntaxLevel, HirSource};
use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use syntax::structure::literal::Literal;
use syntax::structure::traits::Terminator;
use syntax::structure::visitor::{merge_result, Translate};
use syntax::util::translation::{translate_vec, Translatable};
use syntax::util::CompileError;
use syntax::{FunctionRef, Syntax, SyntaxLevel, TypeRef};

/// The MIR level
#[derive(Serialize, Deserialize, Debug)]
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

/// A terminator for a MIR block
#[derive(Serialize, Deserialize, Debug)]
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
#[derive(Serialize, Deserialize, Debug)]
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
            Operand::Constant(literal) => literal.get_type(),
        }
    }
}

/// A location in memory that can be read from or written to
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Place {
    /// Where this place is located
    pub local: LocalVar,
    /// The path to traverse to get to this place
    pub projection: Vec<PlaceElem>,
}

/// A way to traverse a place
#[derive(Serialize, Deserialize, Debug, Copy, Clone)]
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
}

impl<'a> MirContext<'a> {
    /// Creates a new MIR context
    fn new(source: &'a HirSource) -> Self {
        Self { source }
    }
}

impl<'a> MirFunctionContext<'a> {
    /// Creates a MIR function context
    fn new(context: &mut MirContext<'a>) -> Self {
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
            source: &context.source,
        }
    }

    /// Translates a place to its type
    pub fn translate(&self, place: &Place) -> TypeRef {
        let local = self.var_types[place.local];
        for _projection in &place.projection {
            todo!()
        }
        local
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

/// Resolves a HIR source to MIR
pub fn resolve_to_mir(source: HirSource) -> Result<Syntax<MediumSyntaxLevel>, CompileError> {
    source.syntax.translate(&mut MirContext::new(&source))
}

impl<'a, I: SyntaxLevel + Translatable<MirFunctionContext<'a>, I, O>, O: SyntaxLevel>
    Translate<Syntax<O>, MirContext<'a>> for Syntax<I>
{
    fn translate(&self, context: &mut MirContext<'a>) -> Result<Syntax<O>, CompileError> {
        let functions = translate_vec(&self.functions, context, |input, context| {
            I::translate_func(input, &mut MirFunctionContext::new(context))
        });

        let types = translate_vec(&self.types, context, |input, context| {
            I::translate_type(input, &mut MirFunctionContext::new(context))
        });

        let (functions, types) = merge_result(functions, types)?;

        Ok(Syntax {
            symbols: self.symbols.clone(),
            functions,
            types: types.into_iter().flatten().collect(),
        })
    }
}

impl Translatable<MirFunctionContext<'_>, HighSyntaxLevel, MediumSyntaxLevel> for HighSyntaxLevel {
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
        node: &TypeRef,
        context: &mut MirFunctionContext,
    ) -> Result<TypeRef, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_func_ref(
        node: &FunctionRef,
        context: &mut MirFunctionContext,
    ) -> Result<FunctionRef, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_type(
        node: &HighType<HighSyntaxLevel>,
        context: &mut MirFunctionContext,
    ) -> Result<Option<MediumType<MediumSyntaxLevel>>, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_func(
        node: &HighFunction<HighSyntaxLevel>,
        context: &mut MirFunctionContext,
    ) -> Result<MediumFunction<MediumSyntaxLevel>, CompileError> {
        Translate::translate(node, context)
    }

    fn translate_terminator(
        node: &HighTerminator<HighSyntaxLevel>,
        context: &mut MirFunctionContext,
    ) -> Result<MediumTerminator<MediumSyntaxLevel>, CompileError> {
        Translate::translate(node, context)
    }
}

impl<'a, I: SyntaxLevel + Translatable<MirFunctionContext<'a>, I, MediumSyntaxLevel>>
    Translate<MediumTerminator<MediumSyntaxLevel>, MirFunctionContext<'a>> for HighTerminator<I>
{
    fn translate(
        &self,
        context: &mut MirFunctionContext<'a>,
    ) -> Result<MediumTerminator<MediumSyntaxLevel>, CompileError> {
        Ok(match self {
            HighTerminator::Return(returning) => MediumTerminator::Return(
                returning
                    .as_ref()
                    .map(|inner| I::translate_expr(inner, context))
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
