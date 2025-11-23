//! MIR → LIR lowering with monomorphization
//!
//! This module performs the critical transformation from potentially generic MIR
//! to fully monomorphized LIR. The type system enforces that LIR is always concrete.

use crate::*;
use rv_mir::MirType;

/// Lower MIR to LIR with monomorphization
///
/// Takes a collection of MIR functions (which may include generics) and produces
/// fully monomorphized LIR functions ready for LLVM codegen.
pub fn lower_mir_to_lir(
    mir_functions: Vec<rv_mir::MirFunction>,
    _hir_ctx: &rv_hir_lower::LoweringContext,
) -> Vec<LirFunction> {
    let mut lir_functions = Vec::new();

    // Convert all MIR functions to LIR directly (they're already monomorphized by rv-mono)
    for mir_func in mir_functions {
        lir_functions.push(lower_mir_function(&mir_func));
    }

    lir_functions
}

/// Lower a single MIR function to LIR
fn lower_mir_function(mir: &rv_mir::MirFunction) -> LirFunction {
    LirFunction {
        id: mir.id,
        entry_block: mir.entry_block,
        param_count: mir.param_count,
        locals: mir.locals.iter().map(lower_local).collect(),
        basic_blocks: mir.basic_blocks.iter().enumerate().map(|(id, bb)| {
            BasicBlock {
                id,
                statements: bb.statements.iter().map(lower_statement).collect(),
                terminator: lower_terminator(&bb.terminator),
            }
        }).collect(),
    }
}

fn lower_local(local: &rv_mir::Local) -> Local {
    Local {
        id: LocalId(local.id.0),
        name: local.name,
        ty: lower_type(&local.ty),
        mutable: local.mutable,
    }
}

fn lower_type(ty: &MirType) -> LirType {
    match ty {
        MirType::Int => LirType::Int,
        MirType::Float => LirType::Float,
        MirType::Bool => LirType::Bool,
        MirType::Unit => LirType::Unit,
        MirType::String => LirType::String,
        MirType::Named(name) => LirType::Struct { name: *name, fields: vec![] },
        MirType::Struct { name, fields } => LirType::Struct {
            name: *name,
            fields: fields.iter().map(lower_type).collect(),
        },
        MirType::Enum { name, variants } => LirType::Enum {
            name: *name,
            variants: variants.iter().map(|v| LirVariant {
                name: v.name,
                fields: v.fields.iter().map(lower_type).collect(),
            }).collect(),
        },
        MirType::Array { element, size } => LirType::Array {
            element: Box::new(lower_type(element)),
            size: *size,
        },
        MirType::Slice { element } => LirType::Slice {
            element: Box::new(lower_type(element)),
        },
        MirType::Tuple(elements) => LirType::Tuple(elements.iter().map(lower_type).collect()),
        MirType::Ref { mutable, inner } => LirType::Ref {
            mutable: *mutable,
            inner: Box::new(lower_type(inner)),
        },
        MirType::Function { params, ret } => LirType::Function {
            params: params.iter().map(lower_type).collect(),
            ret: Box::new(lower_type(ret)),
        },
    }
}

fn lower_statement(stmt: &rv_mir::Statement) -> Statement {
    match stmt {
        rv_mir::Statement::Assign { place, rvalue, .. } => Statement::Assign {
            place: lower_place(place),
            rvalue: lower_rvalue(rvalue),
        },
        rv_mir::Statement::StorageLive(_) | rv_mir::Statement::StorageDead(_) => {
            // LIR doesn't track storage liveness - convert to Nop
            Statement::Nop
        }
        rv_mir::Statement::Nop => Statement::Nop,
    }
}

fn lower_terminator(term: &rv_mir::Terminator) -> Terminator {
    match term {
        rv_mir::Terminator::Return { value } => Terminator::Return {
            value: value.as_ref().map(lower_operand),
        },
        rv_mir::Terminator::Goto(target) => Terminator::Goto {
            target: *target,
        },
        rv_mir::Terminator::SwitchInt { discriminant, targets, otherwise } => {
            Terminator::SwitchInt {
                discriminant: lower_operand(discriminant),
                targets: targets.iter().map(|(k, v)| (*k as i64, *v)).collect(),
                otherwise: *otherwise,
            }
        },
        rv_mir::Terminator::Call { func, args, destination, target } => {
            Terminator::Call {
                func: *func,
                args: args.iter().map(lower_operand).collect(),
                destination: lower_place(destination),
                target: Some(*target),
            }
        },
        rv_mir::Terminator::Unreachable => Terminator::Unreachable,
    }
}

fn lower_rvalue(rvalue: &rv_mir::RValue) -> RValue {
    match rvalue {
        rv_mir::RValue::Use(op) => RValue::Use(lower_operand(op)),
        rv_mir::RValue::BinaryOp { op, left, right } => RValue::BinaryOp {
            op: *op,
            left: lower_operand(left),
            right: lower_operand(right),
        },
        rv_mir::RValue::UnaryOp { op, operand } => RValue::UnaryOp {
            op: *op,
            operand: lower_operand(operand),
        },
        rv_mir::RValue::Call { func, args, .. } => RValue::Call {
            func: *func,
            args: args.iter().map(lower_operand).collect(),
        },
        rv_mir::RValue::Ref { mutable, place } => RValue::Ref {
            mutable: *mutable,
            place: lower_place(place),
        },
        rv_mir::RValue::Aggregate { kind, operands } => RValue::Aggregate {
            kind: lower_aggregate_kind(kind),
            operands: operands.iter().map(lower_operand).collect(),
        },
    }
}

fn lower_aggregate_kind(kind: &rv_mir::AggregateKind) -> AggregateKind {
    match kind {
        rv_mir::AggregateKind::Tuple => AggregateKind::Tuple,
        rv_mir::AggregateKind::Struct => {
            // Struct name is tracked in the type system, not in the aggregate kind
            AggregateKind::Struct
        }
        rv_mir::AggregateKind::Enum { .. } => {
            // Enum aggregates lowered as struct aggregates
            // (actual enum handling happens through type information)
            AggregateKind::Struct
        }
        rv_mir::AggregateKind::Array(ty) => AggregateKind::Array(lower_type(ty)),
    }
}

fn lower_operand(op: &rv_mir::Operand) -> Operand {
    match op {
        rv_mir::Operand::Copy(place) => Operand::Copy(lower_place(place)),
        rv_mir::Operand::Move(place) => Operand::Move(lower_place(place)),
        rv_mir::Operand::Constant(c) => Operand::Constant(Constant {
            kind: c.kind.clone(),
            ty: lower_type(&c.ty),
            span: rv_span::FileSpan {
                file: rv_span::FileId(0),
                span: rv_span::Span::new(0, 0),
            },
        }),
    }
}

fn lower_place(place: &rv_mir::Place) -> Place {
    Place {
        local: LocalId(place.local.0),
        projection: place.projection.iter().map(lower_projection).collect(),
    }
}

fn lower_projection(proj: &rv_mir::PlaceElem) -> PlaceElem {
    match proj {
        rv_mir::PlaceElem::Deref => PlaceElem::Deref,
        rv_mir::PlaceElem::Field { field_idx } => PlaceElem::Field { field_idx: *field_idx },
        rv_mir::PlaceElem::Index(local) => PlaceElem::Index(LocalId(local.0)),
    }
}
