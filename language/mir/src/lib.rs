pub mod function;
pub mod statement;
pub mod expression;
pub mod types;

use crate::expression::MediumExpression;
use crate::function::MediumFunction;
use crate::statement::MediumStatement;
use crate::types::MediumType;
use hir::expression::HighExpression;
use hir::function::{CodeBlock, HighFunction, HighTerminator};
use hir::statement::HighStatement;
use hir::types::HighType;
use hir::HighSyntaxLevel;
use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use syntax::structure::literal::Literal;
use syntax::structure::traits::Terminator;
use syntax::structure::visitor::Translate;
use syntax::structure::FileOwner;
use syntax::util::path::FilePath;
use syntax::util::translation::Translatable;
use syntax::util::ParseError;
use syntax::{FunctionRef, Syntax, SyntaxLevel, TypeRef};

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

#[derive(Serialize, Deserialize, Debug)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
pub enum MediumTerminator<T: SyntaxLevel> {
    Goto(CodeBlockId),
    Switch {
        discriminant: MediumExpression<T>,
        targets: Vec<(Literal, CodeBlockId)>,
        fallback: CodeBlockId,
    },
    Return(Option<T::Expression>),
    Unreachable,
}

#[derive(Serialize, Deserialize, Debug)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Literal),
}

impl Operand {
    pub fn get_type(&self, context: &MirContext) -> TypeRef {
        match self {
            Operand::Copy(place) => context.translate(place),
            Operand::Move(place) => context.translate(place),
            Operand::Constant(literal) => literal.get_type(),
        }
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Place {
    pub local: LocalVar,
    pub projection: Vec<PlaceElem>,
}

#[derive(Serialize, Deserialize, Debug, Copy, Clone)]
pub enum PlaceElem {
    Deref,
    Field(Spur),
    Index(usize),
}

pub type LocalVar = usize;
pub type CodeBlockId = usize;

impl<T: SyntaxLevel> Terminator for MediumTerminator<T> {}

/// The context for compiling code to MIR. This flattens the syntax tree structure for code
/// into a control-flow graph. Since this means statements and expressions won't map one-to-one,
/// they are instead added to this structure.
pub struct MirContext<'a> {
    file: Option<FilePath>,
    code_blocks: Vec<CodeBlock<MediumSyntaxLevel>>,
    current_block: usize,
    local_vars: HashMap<Spur, LocalVar>,
    var_types: Vec<TypeRef>,
    // The looping condition of the parent control block, if any
    parent_loop: Option<CodeBlockId>,
    // The end of the parent control block, if any
    parent_end: Option<CodeBlockId>,
    syntax: &'a Syntax<HighSyntaxLevel>
}

impl<'a> MirContext<'a> {
    fn new(syntax: &'a Syntax<HighSyntaxLevel>) -> Self {
        Self {
            code_blocks: vec!(CodeBlock {
                statements: vec!(),
                terminator: MediumTerminator::Unreachable
            }),
            syntax,
            file: None,
            current_block: 0,
            local_vars: HashMap::default(),
            var_types: vec!(),
            parent_loop: None,
            parent_end: None,
        }
    }

    pub fn translate(&self, place: &Place) -> TypeRef {
        let local = self.var_types[place.local];
        for _projection in &place.projection {
            todo!()
        }
        local
    }

    // Create a new basic block and return its ID
    pub fn create_block(&mut self) -> CodeBlockId {
        let id = self.code_blocks.len();
        self.code_blocks.push(CodeBlock {
            statements: Vec::new(),
            terminator: MediumTerminator::Unreachable, // Placeholder
        });
        id
    }

    // Switch to a different block for emitting instructions
    pub fn switch_to_block(&mut self, block_id: CodeBlockId) {
        self.current_block = block_id;
    }

    // Add a statement to the current block
    pub fn push_statement(&mut self, statement: MediumStatement<MediumSyntaxLevel>) {
        self.code_blocks[self.current_block].statements.push(statement);
    }

    // Set the terminator for the current block
    pub fn set_terminator(&mut self, terminator: MediumTerminator<MediumSyntaxLevel>) {
        self.code_blocks[self.current_block].terminator = terminator;
    }

    // Create a new temporary variable
    pub fn create_temp(&mut self, type_ref: TypeRef) -> LocalVar {
        self.var_types.push(type_ref);
        self.var_types.len() - 1
    }

    pub fn get_local(&mut self, name: Spur) -> Option<&LocalVar> {
        self.local_vars.get(&name)
    }

    // Get or create a local variable for a named variable
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

impl FileOwner for MirContext<'_> {
    fn file(&self) -> &FilePath {
        self.file.as_ref().unwrap()
    }

    fn set_file(&mut self, file: FilePath) {
        self.file = Some(file);
    }
}

pub fn resolve_to_mir(
    source: Syntax<HighSyntaxLevel>,
) -> Result<Syntax<MediumSyntaxLevel>, ParseError> {
    source.translate(&mut MirContext::new(&source))
}

impl Translatable<MirContext<'_>, HighSyntaxLevel, MediumSyntaxLevel> for HighSyntaxLevel {
    fn translate_stmt(
        node: &HighStatement<HighSyntaxLevel>,
        context: &mut MirContext,
    ) -> Result<MediumStatement<MediumSyntaxLevel>, ParseError> {
        Translate::translate(node, context)
    }

    fn translate_expr(
        node: &HighExpression<HighSyntaxLevel>,
        context: &mut MirContext,
    ) -> Result<MediumExpression<MediumSyntaxLevel>, ParseError> {
        Translate::translate(node, context)
    }

    fn translate_type_ref(node: &TypeRef, context: &mut MirContext) -> Result<TypeRef, ParseError> {
        Translate::<_, _, HighSyntaxLevel, MediumSyntaxLevel>::translate(node, context)
    }

    fn translate_func_ref(
        node: &FunctionRef,
        context: &mut MirContext,
    ) -> Result<FunctionRef, ParseError> {
        Translate::<_, _, HighSyntaxLevel, MediumSyntaxLevel>::translate(node, context)
    }

    fn translate_type(
        node: &HighType<HighSyntaxLevel>,
        context: &mut MirContext,
    ) -> Result<MediumType<MediumSyntaxLevel>, ParseError> {
        Translate::translate(node, context)
    }

    fn translate_func(
        node: &HighFunction<HighSyntaxLevel>,
        context: &mut MirContext,
    ) -> Result<MediumFunction<MediumSyntaxLevel>, ParseError> {
        Translate::translate(node, context)
    }

    fn translate_terminator(node: &HighTerminator<HighSyntaxLevel>, context: &mut MirContext) -> Result<MediumTerminator<MediumSyntaxLevel>, ParseError> {
        Translate::translate(node, context)
    }
}

impl<'a, I: SyntaxLevel + Translatable<MirContext<'a>, I, MediumSyntaxLevel>>
Translate<MediumTerminator<MediumSyntaxLevel>, MirContext<'a>, I, MediumSyntaxLevel> for HighTerminator<I>
{
    fn translate(&self, context: &mut MirContext<'a>) -> Result<MediumTerminator<MediumSyntaxLevel>, ParseError> {
        Ok(match self {
            HighTerminator::Return(returning) => {
                MediumTerminator::Return(
                    Some(returning.as_ref().map(|inner| I::translate_expr(inner, context))
                        .transpose()?.unwrap_or(MediumExpression::Literal(Literal::Void))))
            }
            HighTerminator::Break => MediumTerminator::Goto(*context.parent_end.as_ref().ok_or(
                ParseError::ParseError("Expected to be inside a control block to break from".to_string()))?),
            HighTerminator::Continue => MediumTerminator::Goto(*context.parent_loop.as_ref().ok_or(
                ParseError::ParseError("Expected to be inside a control block to continue".to_string()))?),
            HighTerminator::None => panic!("Failed to set terminator for code block")
        })
    }
}