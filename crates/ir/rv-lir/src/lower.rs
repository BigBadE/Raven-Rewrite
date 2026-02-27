//! MIR → LIR lowering with monomorphization
//!
//! This module performs the critical transformation from potentially generic MIR
//! to fully monomorphized LIR. The type system enforces that LIR is always concrete.

use crate::*;
use rv_hir::{ArraySize, ExternalFunction, FunctionId, TypeId};
use rv_mir::MirType;
use std::collections::HashMap;

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
        return_type: lower_type(&mir.return_type),
        locals: mir.locals.iter().map(lower_local).collect(),
        basic_blocks: mir
            .basic_blocks
            .iter()
            .enumerate()
            .map(|(id, bb)| BasicBlock {
                id,
                statements: bb.statements.iter().map(lower_statement).collect(),
                terminator: lower_terminator(&bb.terminator),
            })
            .collect(),
    }
}

fn lower_local(local: &rv_mir::Local) -> Local {
    Local {
        id: LocalId(local.id.0),
        name: local.name,
        ty: lower_type(&local.ty),
        mutable: local.mutable,
        span: local.span,
    }
}

fn lower_type(ty: &MirType) -> LirType {
    match ty {
        MirType::Int(w, s) => LirType::Int(*w, *s),
        MirType::Float(w) => LirType::Float(*w),
        MirType::Char => LirType::Char,
        MirType::Bool => LirType::Bool,
        MirType::Unit => LirType::Unit,
        MirType::String => LirType::String,
        MirType::Named(name) => {
            panic!(
                "ICE: Unresolved MirType::Named({:?}) reached LIR lowering. \
                 All named types must be resolved to Struct/Enum during MIR type lowering.",
                name
            );
        }
        MirType::Struct { name, fields } => LirType::Struct {
            name: *name,
            fields: fields.iter().map(lower_type).collect(),
        },
        MirType::Enum { name, variants } => LirType::Enum {
            name: *name,
            variants: variants
                .iter()
                .map(|v| LirVariant {
                    name: v.name,
                    fields: v.fields.iter().map(lower_type).collect(),
                })
                .collect(),
        },
        MirType::Array { element, size } => LirType::Array {
            element: Box::new(lower_type(element)),
            size: *size,
        },
        MirType::Slice { element } => LirType::Slice {
            element: Box::new(lower_type(element)),
        },
        MirType::Tuple(elements) => LirType::Tuple(elements.iter().map(lower_type).collect()),
        MirType::Ref {
            mutable,
            inner,
            lifetime,
        } => LirType::Ref {
            mutable: *mutable,
            inner: Box::new(lower_type(inner)),
            lifetime: *lifetime,
        },
        MirType::Function { params, ret } => LirType::Function {
            params: params.iter().map(lower_type).collect(),
            ret: Box::new(lower_type(ret)),
        },
        MirType::Pointer { mutable, inner } => LirType::Pointer {
            mutable: *mutable,
            inner: Box::new(lower_type(inner)),
        },
        MirType::Never => LirType::Never,
        MirType::DynTrait { principal, .. } => LirType::DynTrait {
            principal: *principal,
        },
        MirType::ImplTrait { principal } => LirType::ImplTrait {
            principal: *principal,
        },
        MirType::FunctionPointer { params, ret, abi } => LirType::FunctionPointer {
            params: params.iter().map(lower_type).collect(),
            ret: Box::new(lower_type(ret)),
            abi: abi.clone(),
        },
        MirType::Box { inner } => LirType::Box {
            inner: Box::new(lower_type(inner)),
        },
    }
}

fn lower_statement(stmt: &rv_mir::Statement) -> Statement {
    match stmt {
        rv_mir::Statement::Assign {
            place,
            rvalue,
            span,
        } => Statement::Assign {
            place: lower_place(place),
            rvalue: lower_rvalue(rvalue),
            span: *span,
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
        rv_mir::Terminator::Return { value, .. } => Terminator::Return {
            value: value.as_ref().map(lower_operand),
        },
        rv_mir::Terminator::Goto(target) => Terminator::Goto { target: *target },
        rv_mir::Terminator::SwitchInt {
            discriminant,
            targets,
            otherwise,
            ..
        } => Terminator::SwitchInt {
            discriminant: lower_operand(discriminant),
            targets: targets.iter().map(|(k, v)| (*k as i64, *v)).collect(),
            otherwise: *otherwise,
        },
        rv_mir::Terminator::Call {
            func,
            args,
            destination,
            target,
            ..
        } => Terminator::Call {
            func: *func,
            args: args.iter().map(lower_operand).collect(),
            destination: lower_place(destination),
            target: Some(*target),
        },
        rv_mir::Terminator::Drop { place, target, .. } => Terminator::Drop {
            place: lower_place(place),
            target: *target,
        },
        rv_mir::Terminator::Unreachable => Terminator::Unreachable,
        rv_mir::Terminator::Assert {
            cond,
            expected,
            msg,
            target,
            ..
        } => Terminator::Assert {
            cond: lower_operand(cond),
            expected: *expected,
            msg: lower_assert_message(msg),
            target: *target,
        },
    }
}

fn lower_assert_message(msg: &rv_mir::AssertMessage) -> LirAssertMessage {
    match msg {
        rv_mir::AssertMessage::BoundsCheck { index, len } => LirAssertMessage::BoundsCheck {
            index: lower_operand(index),
            len: lower_operand(len),
        },
        rv_mir::AssertMessage::Overflow(op) => LirAssertMessage::Overflow(*op),
        rv_mir::AssertMessage::DivisionByZero => LirAssertMessage::DivisionByZero,
        rv_mir::AssertMessage::RemainderByZero => LirAssertMessage::RemainderByZero,
        rv_mir::AssertMessage::Panic(s) => LirAssertMessage::Panic(s.clone()),
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
        rv_mir::RValue::Call { func, args } => RValue::Call {
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
        rv_mir::RValue::Discriminant(place) => RValue::Discriminant(lower_place(place)),
        rv_mir::RValue::Cast { operand, from, to } => RValue::Cast {
            operand: lower_operand(operand),
            from: lower_type(from),
            to: lower_type(to),
        },
        rv_mir::RValue::VtableCall {
            receiver,
            vtable_index,
            args,
            trait_id,
            method_name,
        } => RValue::VtableCall {
            receiver: lower_operand(receiver),
            vtable_index: *vtable_index,
            args: args.iter().map(lower_operand).collect(),
            trait_id: *trait_id,
            method_name: *method_name,
        },
        rv_mir::RValue::BoxNew { operand, inner_ty } => RValue::BoxNew {
            operand: lower_operand(operand),
            inner_ty: lower_type(inner_ty),
        },
        rv_mir::RValue::BoxFree { place } => RValue::BoxFree {
            place: lower_place(place),
        },
        rv_mir::RValue::Intrinsic {
            intrinsic,
            args,
            type_args,
        } => RValue::Intrinsic {
            intrinsic: intrinsic.clone(),
            args: args.iter().map(lower_operand).collect(),
            type_args: type_args.iter().map(lower_type).collect(),
        },
    }
}

fn lower_aggregate_kind(kind: &rv_mir::AggregateKind) -> AggregateKind {
    match kind {
        rv_mir::AggregateKind::Tuple => AggregateKind::Tuple,
        rv_mir::AggregateKind::Struct { name } => AggregateKind::Struct { name: *name },
        rv_mir::AggregateKind::Enum { name, variant_idx } => AggregateKind::Enum {
            name: *name,
            variant_idx: *variant_idx,
        },
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
            // MIR constants don't carry spans; use the span from the enclosing statement
            // which is propagated via Statement::Assign.span
            span: rv_span::FileSpan::new(rv_span::FileId(0), rv_span::Span::new(0, 0)),
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
        rv_mir::PlaceElem::Field { field_idx } => PlaceElem::Field {
            field_idx: *field_idx,
        },
        rv_mir::PlaceElem::Index(local) => PlaceElem::Index(LocalId(local.0)),
    }
}

/// Convert an HIR `TypeId` to a concrete `LirType` using the type arena.
///
/// This resolves the type index in the HIR arena and converts the resulting
/// `Type` to a `LirType`. Used primarily for external function declarations
/// where types are stored as HIR `TypeId` references.
pub fn hir_type_to_lir(
    type_id: TypeId,
    types: &la_arena::Arena<rv_hir::Type>,
    interner: &rv_intern::Interner,
) -> LirType {
    let ty = &types[type_id];
    match ty {
        rv_hir::Type::Named { name, .. } => {
            // Resolve well-known type names to concrete LIR types
            let name_str = interner.resolve(name);
            match name_str.as_str() {
                "i8" => LirType::Int(rv_hir::IntWidth::I8, rv_hir::Signedness::Signed),
                "i16" => LirType::Int(rv_hir::IntWidth::I16, rv_hir::Signedness::Signed),
                "i32" => LirType::Int(rv_hir::IntWidth::I32, rv_hir::Signedness::Signed),
                "i64" => LirType::Int(rv_hir::IntWidth::I64, rv_hir::Signedness::Signed),
                "i128" => LirType::Int(rv_hir::IntWidth::I128, rv_hir::Signedness::Signed),
                "isize" => LirType::Int(rv_hir::IntWidth::Isize, rv_hir::Signedness::Signed),
                "u8" => LirType::Int(rv_hir::IntWidth::I8, rv_hir::Signedness::Unsigned),
                "u16" => LirType::Int(rv_hir::IntWidth::I16, rv_hir::Signedness::Unsigned),
                "u32" => LirType::Int(rv_hir::IntWidth::I32, rv_hir::Signedness::Unsigned),
                "u64" => LirType::Int(rv_hir::IntWidth::I64, rv_hir::Signedness::Unsigned),
                "u128" => LirType::Int(rv_hir::IntWidth::I128, rv_hir::Signedness::Unsigned),
                "usize" => LirType::Int(rv_hir::IntWidth::Isize, rv_hir::Signedness::Unsigned),
                "f32" => LirType::Float(rv_hir::FloatWidth::F32),
                "f64" => LirType::Float(rv_hir::FloatWidth::F64),
                "bool" => LirType::Bool,
                "char" => LirType::Char,
                "str" | "String" => LirType::String,
                "()" => LirType::Unit,
                _ => {
                    // Unknown named type — default to i64 as a safe fallback
                    // for the current phase of the compiler
                    LirType::Int(rv_hir::IntWidth::I64, rv_hir::Signedness::Signed)
                }
            }
        }
        rv_hir::Type::Reference {
            mutable,
            inner,
            lifetime,
            ..
        } => LirType::Ref {
            mutable: *mutable,
            inner: Box::new(hir_type_to_lir(**inner, types, interner)),
            lifetime: *lifetime,
        },
        rv_hir::Type::Pointer { mutable, inner, .. } => LirType::Pointer {
            mutable: *mutable,
            inner: Box::new(hir_type_to_lir(**inner, types, interner)),
        },
        rv_hir::Type::Tuple { elements, .. } => LirType::Tuple(
            elements
                .iter()
                .map(|e| hir_type_to_lir(*e, types, interner))
                .collect(),
        ),
        rv_hir::Type::Array { element, size, .. } => {
            let concrete_size = match size {
                ArraySize::Const(n) => *n,
                ArraySize::ConstParam(name) => {
                    panic!(
                        "ICE: Unresolved const parameter '{}' in array size. \
                         All const generics must be resolved before LIR lowering.",
                        interner.resolve(name)
                    );
                }
                ArraySize::Expr(expr) => {
                    panic!(
                        "ICE: Unevaluated const expression '{}' in array size. \
                         All const expressions must be evaluated before LIR lowering.",
                        expr
                    );
                }
                ArraySize::Infer => 0, // Size will be determined from array literal
            };
            LirType::Array {
                element: Box::new(hir_type_to_lir(**element, types, interner)),
                size: concrete_size,
            }
        }
        rv_hir::Type::Function { params, ret, .. } => LirType::Function {
            params: params
                .iter()
                .map(|p| hir_type_to_lir(*p, types, interner))
                .collect(),
            ret: Box::new(hir_type_to_lir(**ret, types, interner)),
        },
        rv_hir::Type::Never { .. } => LirType::Never,
        rv_hir::Type::Generic { name, .. } => {
            panic!(
                "ICE: Unresolved generic type '{}' reached LIR external function lowering. \
                 All generic types must be monomorphized before this stage.",
                interner.resolve(name)
            );
        }
        rv_hir::Type::QualifiedPath { .. }
        | rv_hir::Type::DynTrait { .. }
        | rv_hir::Type::ImplTrait { .. }
        | rv_hir::Type::Unknown { .. } => {
            panic!(
                "ICE: Unresolved abstract type {:?} reached LIR external function lowering. \
                 All types must be concrete before this stage.",
                &types[type_id]
            );
        }
    }
}

/// Lower HIR external functions to LIR external functions with resolved types.
///
/// Converts `ExternalFunction` (which stores HIR `TypeId` references) into
/// `LirExternalFunction` (which stores concrete `LirType` values).
pub fn lower_external_functions(
    external_funcs: &HashMap<FunctionId, ExternalFunction>,
    types: &la_arena::Arena<rv_hir::Type>,
    interner: &rv_intern::Interner,
) -> HashMap<FunctionId, LirExternalFunction> {
    external_funcs
        .iter()
        .map(|(id, ext)| {
            let param_types = ext
                .parameters
                .iter()
                .map(|param| hir_type_to_lir(param.ty, types, interner))
                .collect();
            let return_type = ext
                .return_type
                .map(|ty_id| hir_type_to_lir(ty_id, types, interner));

            let lir_ext = LirExternalFunction {
                id: *id,
                name: ext.name,
                mangled_name: ext.mangled_name.clone(),
                param_types,
                return_type,
                abi: ext.abi.clone(),
            };
            (*id, lir_ext)
        })
        .collect()
}
