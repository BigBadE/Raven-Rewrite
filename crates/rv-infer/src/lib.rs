//! Inference/elaboration: `IR<Parsed>` -> `IR<Lowerable>` + verification obligations.
//!
//! Two jobs, both performed by [`elaborate`]:
//!
//! 1. **Type inference** — `Parsed` loses local/param/return types (they are `()`).
//!    A forward pass assigns each local a [`rv_core::Ty`] from the `RValue` that
//!    defines it (arithmetic -> `Int`, comparison/logic -> `Bool`, `Const` -> its
//!    type, `Call` -> the callee's return type). The program is rebuilt into the
//!    `Lowerable` phase, filling `LocalDecl.ty`, `Function.ret`, and (for any
//!    `Drop` terminator) a placeholder default `DisciplineId(0)`.
//!
//! 2. **VC generation** — forward symbolic execution over each function's CFG,
//!    emitting [`rv_logic::Obligation`]s for division safety, `assert`s, call
//!    preconditions (modular verification) and postconditions.
//!
//! This pass also handles algebraic data types (`Aggregate` rvalues + `Field`/
//! `Downcast` projections — modeled as opaque symbolic vars since the kernel
//! `Term` has no ADT constructors), `match` (exhaustiveness checking + per-arm
//! path exploration), and loop invariants (`Stmt::Invariant` headers).
//!
//! ## Generics (lenient but sound)
//!
//! A generic type parameter `Ty::Param(_)` (e.g. `T` in `fn id<T>(x: T) -> T`, or a
//! generic ADT field declared `T`) is treated as an *opaque* type:
//!
//! * Type arguments are **erased**: a `Function`'s `type_params` are carried through
//!   the phase change unchanged, and a generic ADT value still types as `Ty::Adt(name)`
//!   (we never track type arguments). Match exhaustiveness uses the variant count from
//!   the `TypeDef`, which a type parameter does not affect.
//! * In [`resolve_proj_ty`], a field whose declared type is `Ty::Param(_)` stays
//!   `Ty::Param(_)` (opaque); a `Field`/`Downcast` off an unknown/param base falls back
//!   to the `Int` default, as before.
//! * In [`check`]/[`set_ty`], an operand of `Ty::Param(_)` is *never* a type error — a
//!   generic body is checked abstractly (e.g. `return x` with `x: T` yields `T`). Only
//!   concretely-conflicting non-generic types are rejected, exactly as before.
//!
//! This is **sound**: a `Ty::Param` value behaves like any other non-scalar — reads/uses
//! produce *fresh opaque `Term::Var`s* in VC generation, so we never assume a fact about a
//! generic value. We only forgo *rejecting* a generic body; we never *prove* something false.
//!
//! ## Known limitations (foundation, reported not worked around)
//!
//! * **ADT internals are opaque.** The kernel `Term` has only `Int`/`Bool`/`Var`
//!   plus arithmetic/logic — no constructors or field selectors. So every
//!   aggregate value and every field/variant read becomes a *fresh opaque
//!   `Term::Var`*. Obligations about an ADT's internals are therefore not
//!   provable; we verify the int/bool parts of a program, which is sound (we lose
//!   provability, never gain it). Lifting this needs `rv-core` to grow ADT terms.
//! * **Loops WITHOUT an invariant are still not verified** — a back-edge to an
//!   already-visited block just stops that path (the original demo behavior).
//!   Loops that DO carry `Stmt::Invariant` headers get the inductive scheme in
//!   [`VcGen::exec_loop_header`] (entry + havoc/assume + preservation), which is
//!   simplified but soundness-leaning; see that method's caveats.

use std::collections::{HashMap, HashSet};

use rv_core::{BinOp, Prop, Sym, Symbols, Term, Ty, UnOp};
use rv_ir::{
    AggKind, Block, BlockId, Const, DisciplineId, Function, Lowerable, LocalId, Operand, Parsed,
    Place, Proj, Program, RValue, Stmt, Terminator, TypeDef, RESULT_NAME,
};

/// The result of elaboration: a typed (`Lowerable`) program plus the verification
/// obligations its symbolic execution produced.
pub struct Elaborated {
    pub prog: Program<Lowerable>,
    pub obligations: Vec<rv_logic::Obligation>,
}

/// Elaborate a parsed program: infer types (producing a `Lowerable` program) and
/// generate verification conditions. Returns `Err` on a static type error.
pub fn elaborate(prog: Program<Parsed>, syms: &Symbols) -> Result<Elaborated, String> {
    // We need a *mutable* symbol table to mint fresh call-result variables, but the
    // public API only lends us `&Symbols`. Clone it locally; fresh names never need
    // to escape this pass (they only appear inside obligations).
    let mut syms = syms.clone();

    // Map each function name -> its (params, pre, post, return-type) signature, so
    // call sites can do modular verification and pick up callee return types.
    let mut sigs: HashMap<Sym, Signature> = HashMap::new();

    // Index the user-defined types by name so inference (ADT typing) and VC
    // generation (match exhaustiveness) can look them up in O(1).
    let type_table: HashMap<Sym, TypeDef> =
        prog.types.iter().map(|t| (t.name(), t.clone())).collect();

    // ---- Pass 1: infer per-function types, build the Lowerable program. ----
    // Seed direct-call typing from surface return annotations. A function may call a
    // later declaration, so this map must exist before any body is inferred.
    let declared_returns: HashMap<Sym, Ty> = prog
        .funcs
        .iter()
        .map(|f| (f.name, f.ret.clone().unwrap_or(Ty::Int)))
        .collect();
    let mut provisional: Vec<Function<Lowerable>> = Vec::with_capacity(prog.funcs.len());
    for f in &prog.funcs {
        provisional.push(infer_function(f, &type_table, &declared_returns, None)?);
    }

    // A small second pass replaces annotation fallbacks with the actual inferred
    // return types. This covers unannotated/lifted functions without making the
    // answer depend on declaration order.
    let inferred_returns: HashMap<Sym, Ty> = provisional
        .iter()
        .map(|f| (f.name, f.ret.clone()))
        .collect();
    let call_types = callable_types(&provisional);
    let mut funcs_low: Vec<Function<Lowerable>> = Vec::with_capacity(prog.funcs.len());
    for f in &prog.funcs {
        let inferred = infer_function(f, &type_table, &inferred_returns, Some(&call_types))?;
        sigs.insert(
            f.name,
            Signature {
                param_syms: param_syms(f),
                pre: f.pre.clone(),
                post: f.post.clone(),
            },
        );
        funcs_low.push(inferred);
    }

    // ---- Pass 2: VC generation via forward symbolic execution. ----
    let mut obligations = Vec::new();
    for (f, low) in prog.funcs.iter().zip(funcs_low.iter()) {
        // Exhaustiveness is a static check over the (typed) function; run it before
        // symbolic execution so a non-exhaustive match fails fast.
        check_exhaustiveness(low, &type_table)?;
        let mut vc = VcGen {
            f,
            low,
            types: &type_table,
            sigs: &sigs,
            syms: &mut syms,
            obligations: &mut obligations,
        };
        vc.run(low);
    }

    // Carry the (phase-independent) type definitions through to the Lowerable
    // program unchanged.
    Ok(Elaborated { prog: Program { types: prog.types, funcs: funcs_low }, obligations })
}

/// A callee's signature, used at call sites for modular verification.
struct Signature {
    /// Parameter *symbols* (the names `pre`/`post` are written against), in order.
    param_syms: Vec<Sym>,
    pre: Prop,
    post: Prop,
}

/// The executable portion of a function type used while inferring call sites.
/// Contracts remain in [`Signature`] for VC generation; this shape is deliberately
/// structural so it can become one component of a unified callable type later.
struct CallableType {
    params: Vec<Ty>,
    ret: Ty,
}

fn callable_types(funcs: &[Function<Lowerable>]) -> HashMap<Sym, CallableType> {
    funcs
        .iter()
        .map(|f| {
            let params = f
                .params
                .iter()
                .map(|id| f.locals[id.0 as usize].ty.clone())
                .collect();
            (f.name, CallableType { params, ret: f.ret.clone() })
        })
        .collect()
}

/// The parameter symbols of a function, in parameter order. Missing names (anonymous
/// params) are skipped — `pre`/`post` cannot refer to them anyway.
fn param_syms<P: rv_ir::Phase>(f: &Function<P>) -> Vec<Sym> {
    f.params.iter().filter_map(|p| f.locals[p.0 as usize].name).collect()
}

// ===========================================================================
// Pass 1: type inference
// ===========================================================================

/// Infer a single function's local/return types and rebuild it in the `Lowerable`
/// phase. A forward pass assigns each local the type of the `RValue` defining it.
fn infer_function(
    f: &Function<Parsed>,
    types: &HashMap<Sym, TypeDef>,
    returns: &HashMap<Sym, Ty>,
    calls: Option<&HashMap<Sym, CallableType>>,
) -> Result<Function<Lowerable>, String> {
    // Seed from any front-end *declared* types (e.g. a parameter's `: u8`), then
    // refine by the forward sweep over assignments. A declared type matters most
    // for a parameter (no defining assignment to infer its type from) and for
    // recovering a sized-integer width that drives overflow bounds.
    let mut tys: Vec<Option<Ty>> = f.locals.iter().map(|d| d.ty.clone()).collect();

    // Walk blocks in id order; for branching code a single forward sweep over all
    // assignments is enough to type every defined local.
    //
    // A projection in the assignment target (`Field`/`Downcast`) means we are
    // writing *into* a component of an ADT local, not redefining the local — so we
    // only record the local's type for projection-free assignments. (For the
    // match-binding pattern, the binder local is a fresh local that gets its own
    // ADT/scalar type via a normal copy elsewhere; we default unknown locals to
    // `Int` as before.)
    for blk in &f.blocks {
        for stmt in &blk.stmts {
            if let Stmt::Assign(place, rv) = stmt {
                if !place.proj.is_empty() {
                    continue;
                }
                let ty = type_of_rvalue(rv, &tys, f, types, returns, calls)?;
                set_ty(&mut tys, place.local, ty)?;
            }
        }
    }

    // Return type: from the operand of a `Return` terminator (first one found).
    let mut ret = Ty::Unit;
    for blk in &f.blocks {
        if let Terminator::Return(op) = &blk.term {
            ret = type_of_operand(op, &tys, types)?;
            break;
        }
    }

    // Soundness: if the signature *declared* a return type, the body must agree with it.
    // We enforce this conservatively — only between *primitive scalars* — so a `bool` body
    // under an `-> i64` signature (and vice versa) is rejected, while ADT/ref/opaque returns
    // (whose operand type may be defaulted) are left to the existing lenient inference.
    if let Some(declared) = &f.ret {
        check_scalar_return(&ret, declared)?;
    }

    // Any local still unknown defaults to `Int` (the pragmatic default for the slice;
    // a local with no defining assignment we can pin is treated as a numeric).
    let locals = f
        .locals
        .iter()
        .enumerate()
        .map(|(i, d)| rv_ir::LocalDecl { name: d.name, ty: tys[i].clone().unwrap_or(Ty::Int) })
        .collect();

    let blocks = f.blocks.iter().map(rebuild_block).collect();

    Ok(Function {
        name: f.name,
        // Generic type parameters are erased for checking but carried through the
        // phase change so downstream phases see the same signature.
        type_params: f.type_params.clone(),
        params: f.params.clone(),
        ret,
        pre: f.pre.clone(),
        post: f.post.clone(),
        locals,
        blocks,
        entry: f.entry,
    })
}

/// Record an inferred type for a local, erroring on a conflicting re-inference.
fn set_ty(tys: &mut [Option<Ty>], local: LocalId, ty: Ty) -> Result<(), String> {
    let slot = &mut tys[local.0 as usize];
    match slot {
        // GENERIC LENIENCY: if either the existing or the new inference is an opaque
        // type parameter, do not treat the difference as a conflict — a generic local
        // is abstract. Keep whichever is concrete (prefer a concrete type over `Param`)
        // so later concrete checks still see the most specific type we know.
        Some(existing) if matches!(existing, Ty::Param(_)) || matches!(ty, Ty::Param(_)) => {
            if matches!(existing, Ty::Param(_)) {
                *slot = Some(ty);
            }
            Ok(())
        }
        // INTEGER LENIENCY: a sized `IntN` and the default `Int` are compatible
        // (e.g. a `u8` local assigned an `Int` literal). Keep the sized width — it
        // is the more specific type and carries the overflow bounds.
        Some(existing) if int_like(existing) && int_like(&ty) => {
            if matches!(existing, Ty::Int) && matches!(ty, Ty::IntN(_)) {
                *slot = Some(ty);
            }
            Ok(())
        }
        Some(existing) if *existing != ty => {
            Err(format!("type error: local {} used as both {:?} and {:?}", local.0, existing, ty))
        }
        _ => {
            *slot = Some(ty);
            Ok(())
        }
    }
}

/// The type an `RValue` produces. Also catches static type errors (e.g. arithmetic
/// on a known-`Bool` operand).
fn type_of_rvalue(
    rv: &RValue,
    tys: &[Option<Ty>],
    f: &Function<Parsed>,
    types: &HashMap<Sym, TypeDef>,
    returns: &HashMap<Sym, Ty>,
    calls: Option<&HashMap<Sym, CallableType>>,
) -> Result<Ty, String> {
    match rv {
        RValue::Use(op) => type_of_operand(op, tys, types),
        RValue::Bin(op, a, b) | RValue::WrappingBin(op, a, b) => {
            let (ta, tb) = (type_of_operand(a, tys, types)?, type_of_operand(b, tys, types)?);
            use BinOp::*;
            match op {
                // Arithmetic preserves the integer width: if either operand is a
                // sized `IntN`, so is the result (used to pick overflow bounds).
                // Bitwise/shift ops are integer-typed too (no overflow obligation
                // is emitted for them — that check is gated on `Add|Sub|Mul`).
                // Float arithmetic: if either operand is a float, the result is a float (no
                // overflow obligation — floats are opaque to the linear solver).
                Add | Sub | Mul | Div | Mod if matches!(ta, Ty::Float) || matches!(tb, Ty::Float) => {
                    Ok(Ty::Float)
                }
                Add | Sub | Mul | Div | Mod | BitAnd | BitOr | BitXor | Shl | Shr => {
                    int_result_ty(&ta, &tb).ok_or_else(|| "arithmetic on non-integers".to_string())
                }
                And | Or => {
                    check(&ta, &Ty::Bool, "logic")?;
                    check(&tb, &Ty::Bool, "logic")?;
                    Ok(Ty::Bool)
                }
                Eq | Ne => Ok(Ty::Bool),
                Lt | Le | Gt | Ge => {
                    if (int_like(&ta) && int_like(&tb))
                        || (matches!(ta, Ty::Float) || matches!(tb, Ty::Float))
                    {
                        Ok(Ty::Bool)
                    } else {
                        Err("comparison on non-integers".to_string())
                    }
                }
            }
        }
        RValue::Un(op, a) => {
            let ta = type_of_operand(a, tys, types)?;
            match op {
                UnOp::Neg => {
                    if int_like(&ta) {
                        Ok(ta)
                    } else {
                        Err("negation of a non-integer".to_string())
                    }
                }
                UnOp::Not => {
                    check(&ta, &Ty::Bool, "not")?;
                    Ok(Ty::Bool)
                }
            }
        }
        // A call has its callee's declared/inferred return type. The map is seeded
        // from every declaration before body inference and then refreshed with
        // actual inferred returns, so forward calls and lifted functions are not
        // silently treated as `i64`.
        RValue::Call(callee, args) => {
            let _ = f;
            let sig = calls.and_then(|calls| calls.get(callee));
            if let Some(sig) = sig {
                if args.len() != sig.params.len() {
                    return Err(format!(
                        "type error: call expects {} arguments, got {}",
                        sig.params.len(),
                        args.len()
                    ));
                }
                for (index, (arg, param)) in args.iter().zip(&sig.params).enumerate() {
                    let arg_ty = type_of_operand(arg, tys, types)?;
                    check(&arg_ty, param, &format!("argument {} of call", index + 1))?;
                }
                return Ok(sig.ret.clone());
            }
            Ok(returns.get(callee).cloned().unwrap_or(Ty::Int))
        }
        // A closure value has a function type. We do not track the lambda's exact
        // signature here (it is opaque to the kernel anyway), so we give it a
        // best-effort `Fn` type; closure locals are never indexed/len'd, so the
        // imprecise arg/ret types are inconsequential.
        RValue::Closure(_func, _captures) => Ok(Ty::Fn(vec![], Box::new(Ty::Int))),
        // An indirect call's result type is unknown; default to the numeric `Int`,
        // exactly as a direct `Call` does.
        RValue::CallClosure(_callee, _) => Ok(Ty::Int),
        // Aggregates name their ADT directly: a struct `s` has type `Adt(s)`, an
        // enum variant of `e` has type `Adt(e)`. The local *is* the ADT value.
        RValue::Aggregate(AggKind::Struct(s), _) => Ok(Ty::Adt(*s)),
        RValue::Aggregate(AggKind::Variant(e, _), _) => Ok(Ty::Adt(*e)),
        // A tuple's type is the tuple of its operands' types.
        RValue::Aggregate(AggKind::Tuple, ops) => {
            let elems = ops
                .iter()
                .map(|op| type_of_operand(op, tys, types))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Ty::Tuple(elems))
        }
        // A fixed array's type is `[elem; len]`; `elem` is the first element's
        // type (homogeneous), defaulting to `Int` for an empty literal.
        RValue::Aggregate(AggKind::Array, ops) => {
            let elem = match ops.first() {
                Some(op) => type_of_operand(op, tys, types)?,
                None => Ty::Int,
            };
            Ok(Ty::Array(Box::new(elem), ops.len()))
        }
        // A `Vec<T>` literal / `Vec::new()`; `T` is the first element's type.
        RValue::Aggregate(AggKind::Vec, ops) => {
            let elem = match ops.first() {
                Some(op) => type_of_operand(op, tys, types)?,
                None => Ty::Int,
            };
            Ok(Ty::Vec(Box::new(elem)))
        }
        // `v.len()` is an integer; `push` yields the (grown) vector's type.
        RValue::VecLen(_) => Ok(Ty::Int),
        RValue::VecPush(v, _) => type_of_operand(v, tys, types),
        // A borrow `&place` / `&mut place` has type `Ref { mutable, inner }`, where
        // `inner` is the *type of the borrowed place* (the base local's type followed
        // through its projections). `BorrowKind::Mut` sets `mutable: true`.
        RValue::Ref(kind, place) => {
            let _ = f;
            let base = tys[place.local.0 as usize].clone().unwrap_or(Ty::Int);
            let inner = resolve_proj_ty(&base, &place.proj, types);
            Ok(Ty::Ref {
                mutable: matches!(kind, rv_ir::BorrowKind::Mut),
                inner: Box::new(inner),
            })
        }
    }
}

/// The type of an operand: a constant's own type, or a local's so-far-inferred type.
/// A not-yet-known local defaults to `Int`, so a forward sweep is robust to order.
fn type_of_operand(
    op: &Operand,
    tys: &[Option<Ty>],
    types: &HashMap<Sym, TypeDef>,
) -> Result<Ty, String> {
    Ok(match op {
        Operand::Const(Const::Int(_)) => Ty::Int,
        Operand::Const(Const::Float(_)) => Ty::Float,
        Operand::Const(Const::Str(_)) => Ty::Str,
        Operand::Const(Const::Bool(_)) => Ty::Bool,
        Operand::Const(Const::Unit) => Ty::Unit,
        Operand::Copy(place) => {
            let base = tys[place.local.0 as usize].clone().unwrap_or(Ty::Int);
            resolve_proj_ty(&base, &place.proj, types)
        }
    })
}

/// Resolve the type reached by following `proj` (struct field / enum downcast+field)
/// from a base type. Falls back to `Int` when the path can't be resolved (base type
/// unknown / not an ADT), which is safe for the slice's scalar-focused verification.
fn resolve_proj_ty(base: &Ty, proj: &[Proj], types: &HashMap<Sym, TypeDef>) -> Ty {
    let mut cur = base.clone();
    // The variant most recently selected by a `Downcast`, used by the next `Field`.
    let mut variant: u32 = 0;
    for p in proj {
        match p {
            Proj::Downcast(v) => variant = *v,
            // Dereferencing a reference `&T`/`&mut T` yields its pointee type `T`.
            // A `Deref` off a non-reference type can't be resolved (e.g. an opaque /
            // defaulted local); fall back to `Int`, which is safe for the slice's
            // scalar-focused verification.
            Proj::Deref => {
                cur = match cur {
                    Ty::Ref { inner, .. } => *inner,
                    _ => Ty::Int,
                };
                variant = 0;
            }
            Proj::Field(n) => {
                // A tuple field projects positionally to its element type.
                if let Ty::Tuple(elems) = &cur {
                    cur = elems.get(*n as usize).cloned().unwrap_or(Ty::Int);
                    variant = 0;
                    continue;
                }
                let Ty::Adt(name) = &cur else { return Ty::Int };
                let field_ty = match types.get(name) {
                    Some(TypeDef::Struct { fields, .. }) => {
                        fields.get(*n as usize).map(|fd| fd.ty.clone())
                    }
                    Some(TypeDef::Enum { variants, .. }) => variants
                        .get(variant as usize)
                        .and_then(|vd| vd.fields.get(*n as usize).cloned()),
                    None => None,
                };
                cur = field_ty.unwrap_or(Ty::Int);
                variant = 0;
            }
            // Indexing an array yields its element type.
            Proj::Index(_) => {
                cur = match cur {
                    Ty::Array(elem, _) => *elem,
                    _ => Ty::Int,
                };
                variant = 0;
            }
        }
    }
    cur
}

/// Conjoin the range fact `w.min <= term <= w.max` for a sized-integer value
/// onto a path. Used to record that an `IntN` parameter / result is in range.
fn range_assumption(path: Prop, term: &Term, w: rv_core::IntTy) -> Prop {
    let lo = Prop::Holds(Term::bin(BinOp::Ge, term.clone(), Term::Int(w.min() as i64)));
    let hi = Prop::Holds(Term::bin(BinOp::Le, term.clone(), Term::Int(w.max() as i64)));
    path.and(lo).and(hi)
}

/// Whether a type can take part in integer arithmetic: the default `Int`, a
/// sized `IntN`, or an opaque generic `Param` (checked abstractly).
fn int_like(t: &Ty) -> bool {
    matches!(t, Ty::Int | Ty::IntN(_) | Ty::Param(_))
}

/// The result type of integer arithmetic on `a` and `b`: a sized `IntN` width is
/// preserved (it carries the overflow bounds); otherwise the default `Int`.
/// `None` if either operand is not integer-like.
fn int_result_ty(a: &Ty, b: &Ty) -> Option<Ty> {
    if !int_like(a) || !int_like(b) {
        return None;
    }
    match (a, b) {
        (Ty::IntN(w), _) | (_, Ty::IntN(w)) => Some(Ty::IntN(*w)),
        _ => Some(Ty::Int),
    }
}

/// Classify a type as a primitive scalar: `Some(true)` = boolean, `Some(false)` =
/// integer-family (`Int`/`IntN`). Everything else (ADT, ref, unit, fn, param) is `None`.
fn scalar_kind(t: &Ty) -> Option<bool> {
    match t {
        Ty::Bool => Some(true),
        Ty::Int | Ty::IntN(_) => Some(false),
        _ => None,
    }
}

/// Reject a primitive-scalar return mismatch (the `bool` body / `-> i64` signature bug).
/// Only fires when *both* the body's type and the declared type are primitive scalars and
/// they disagree on the boolean/integer axis — `Int` vs `IntN` stays compatible, and any
/// non-scalar (ADT/ref/opaque) is left to the lenient inference path.
fn check_scalar_return(actual: &Ty, declared: &Ty) -> Result<(), String> {
    if let (Some(a), Some(d)) = (scalar_kind(actual), scalar_kind(declared)) {
        if a != d {
            return Err(format!(
                "type error in return type: signature declares {declared:?}, but the body returns {actual:?}"
            ));
        }
    }
    Ok(())
}

fn check(got: &Ty, want: &Ty, ctx: &str) -> Result<(), String> {
    // GENERIC LENIENCY: a value of a generic type parameter (`Ty::Param`) is opaque
    // — a generic body is checked abstractly, so we cannot (and must not) reject it
    // against a concrete expectation. Treating `Param` as compatible with anything
    // never *adds* facts (the value stays an opaque `Term::Var` in VC generation), so
    // this is sound: we only forgo rejecting a generic body, never prove something false.
    if matches!(got, Ty::Param(_)) || matches!(want, Ty::Param(_)) {
        return Ok(());
    }
    if got == want {
        Ok(())
    } else {
        Err(format!("type error in {ctx}: expected {want:?}, got {got:?}"))
    }
}

/// Rebuild a block into the `Lowerable` phase. Statements are phase-independent, so
/// only the terminator's phase parameter changes (and `Drop` gains a strategy).
fn rebuild_block(blk: &Block<Parsed>) -> Block<Lowerable> {
    Block { id: blk.id, stmts: blk.stmts.clone(), term: rebuild_term(&blk.term) }
}

fn rebuild_term(term: &Terminator<Parsed>) -> Terminator<Lowerable> {
    match term {
        Terminator::Goto(b) => Terminator::Goto(*b),
        Terminator::Branch { cond, then_blk, else_blk } => {
            Terminator::Branch { cond: cond.clone(), then_blk: *then_blk, else_blk: *else_blk }
        }
        Terminator::Return(op) => Terminator::Return(op.clone()),
        // A `panic` aborts; it is phase-independent (no successors, no strategy).
        Terminator::Panic => Terminator::Panic,
        Terminator::Match { scrutinee, arms, otherwise } => Terminator::Match {
            scrutinee: scrutinee.clone(),
            arms: arms.clone(),
            otherwise: *otherwise,
        },
        // Lowering does not emit Drop in this slice, but rebuild it faithfully if
        // present, filling the placeholder "default" discipline.
        Terminator::Drop { place, strategy: (), next } => {
            Terminator::Drop { place: place.clone(), strategy: DisciplineId(0), next: *next }
        }
    }
}

// ===========================================================================
// Match exhaustiveness
// ===========================================================================

/// Statically reject any `Match` that is not exhaustive: if there is no
/// `otherwise` arm and the explicit arms do not cover all of the scrutinee
/// enum's variant indices, elaboration fails.
///
/// The scrutinee's enum is found from its inferred ADT type (filled into
/// `LocalDecl.ty` during inference). If we cannot resolve the scrutinee to a
/// concrete enum (e.g. it is an opaque/defaulted local, or a struct), we
/// conservatively skip the check — an enum match always types its scrutinee as
/// `Adt(enum)`, so well-formed enum matches are covered.
fn check_exhaustiveness(
    f: &Function<Lowerable>,
    types: &HashMap<Sym, TypeDef>,
) -> Result<(), String> {
    for blk in &f.blocks {
        if let Terminator::Match { scrutinee, arms, otherwise } = &blk.term {
            // A catch-all arm always makes the match exhaustive.
            if otherwise.is_some() {
                continue;
            }
            // Resolve the scrutinee's enum and its variant count.
            let Some(n_variants) = scrutinee_variant_count(scrutinee, f, types) else {
                continue;
            };
            // Collect the covered variant indices.
            let covered: HashSet<u32> = arms.iter().map(|a| a.variant).collect();
            let all_covered = (0..n_variants as u32).all(|v| covered.contains(&v));
            if !all_covered {
                return Err("non-exhaustive match".to_string());
            }
        }
    }
    Ok(())
}

/// The number of variants of the enum the scrutinee operand has, if it resolves
/// to a concrete enum type in `types`. `None` if not a (resolvable) enum.
fn scrutinee_variant_count(
    scrutinee: &Operand,
    f: &Function<Lowerable>,
    types: &HashMap<Sym, TypeDef>,
) -> Option<usize> {
    let Operand::Copy(place) = scrutinee else { return None };
    let ty = &f.locals[place.local.0 as usize].ty;
    let Ty::Adt(name) = ty else { return None };
    match types.get(name) {
        Some(TypeDef::Enum { variants, .. }) => Some(variants.len()),
        _ => None,
    }
}

// ===========================================================================
// Pass 2: VC generation (forward symbolic execution)
// ===========================================================================

/// Symbolic-execution state threaded along a single CFG path. Cloned per branch.
#[derive(Clone)]
struct State {
    /// Each local's current symbolic value.
    env: HashMap<LocalId, Term>,
    /// Conjunction of branch conditions + assumes taken so far (the hypotheses).
    path: Prop,
    /// Blocks already entered on this path — the back-edge / loop guard.
    visited: HashSet<BlockId>,
    /// Loop headers we are currently *inside* (header -> its invariants). A
    /// back-edge to one of these emits the "loop invariant preserved" obligation.
    loop_headers: HashMap<BlockId, Vec<Prop>>,
    /// Points-to facts: a reference local `r` created by `r = &x` / `r = &mut x`
    /// with a *bare local* pointee maps `r ↦ x`. This lets the verifier read and
    /// (for `&mut`) strong-update the pointee's symbolic value through `*r`.
    ///
    /// SOUNDNESS rests on the borrow checker: a `&mut x` is *unique* while live
    /// (no other live reference aliases `x`, and `x` cannot be reassigned while
    /// borrowed), so a store `*r = e` is a strong update to `x` — exactly one
    /// location changes. A program that violates the borrow discipline is never
    /// reported verified (the driver conjoins `borrow_errors.is_empty()` with the
    /// obligation results), so these facts are only *relied upon* when the
    /// uniqueness that justifies them actually holds. This is the ownership →
    /// dependency bridge: unique ownership licenses reasoning about pointee values.
    points_to: HashMap<LocalId, LocalId>,
}

/// Carries everything a function's VC walk needs.
struct VcGen<'a> {
    f: &'a Function<Parsed>,
    /// The typed (Lowerable) view of the same function — used to resolve a
    /// place's type (e.g. an array's length) when emitting bounds obligations.
    low: &'a Function<Lowerable>,
    types: &'a HashMap<Sym, TypeDef>,
    sigs: &'a HashMap<Sym, Signature>,
    syms: &'a mut Symbols,
    obligations: &'a mut Vec<rv_logic::Obligation>,
}

impl VcGen<'_> {
    /// Run symbolic execution from the entry block.
    fn run(&mut self, low: &Function<Lowerable>) {
        // Initialize parameters to their named symbolic variables. A sized-integer
        // (`IntN`) parameter additionally carries the implicit fact that its value
        // is within the type's range — the invariant that makes width-checked
        // arithmetic on it provable (sound: an `IntN` value is *always* in range,
        // by construction of its producers).
        let mut env = HashMap::new();
        let mut path = self.f.pre.clone();
        for p in &self.f.params {
            if let Some(name) = low.locals[p.0 as usize].name {
                let var = Term::Var(name);
                if let Ty::IntN(w) = &low.locals[p.0 as usize].ty {
                    path = range_assumption(path, &var, *w);
                }
                env.insert(*p, var);
            }
        }
        let state = State {
            env,
            path,
            visited: HashSet::new(),
            loop_headers: HashMap::new(),
            points_to: HashMap::new(),
        };
        self.exec_block(self.f.entry, state);
    }

    /// Look up a block by id (CFGs here are small; linear search is fine).
    fn block(&self, id: BlockId) -> &Block<Parsed> {
        self.f.blocks.iter().find(|b| b.id == id).expect("dangling block id")
    }

    /// Symbolically execute a block and recurse into its successors.
    fn exec_block(&mut self, id: BlockId, mut state: State) {
        // A block whose first statements are `Invariant`s is a loop header. The
        // FIRST time we reach it on this path we switch to the invariant scheme
        // (entry check + havoc/assume + one body pass) instead of plain forward
        // execution. The scheme marks the header visited so the back-edge stops.
        if !state.visited.contains(&id) && self.loop_invariants(id).is_some() {
            self.exec_loop_header(id, state);
            return;
        }

        // Loop guard: a back-edge into an already-visited block stops this path.
        // If that block is a loop header we are inside, this back-edge is the end
        // of one symbolic iteration: prove each invariant is PRESERVED (under the
        // body-end path) before stopping. Invariant-free loops keep the original
        // "stop at back-edge" demo behavior.
        if !state.visited.insert(id) {
            if let Some(invs) = state.loop_headers.get(&id).cloned() {
                for inv in &invs {
                    let goal = self.resolve_names(inv, &state);
                    self.emit(state.path.clone(), goal, "loop invariant preserved");
                }
            }
            return;
        }
        // Clone the block out so we don't hold a borrow of `self` across the
        // `&mut self` statement/terminator calls below.
        let blk_idx = self.f.blocks.iter().position(|b| b.id == id).expect("dangling block id");

        let stmts = self.f.blocks[blk_idx].stmts.clone();
        for stmt in &stmts {
            self.exec_stmt(stmt, &mut state);
        }

        self.exec_terminator(id, state);
    }

    /// Execute a block's terminator, recursing into successors. Factored out so the
    /// loop-header path can reuse it after the havoc/assume setup.
    fn exec_terminator(&mut self, id: BlockId, state: State) {
        // Re-borrow the terminator (immutably) via a clone of what we need.
        match self.block(id).term {
            Terminator::Goto(b) => self.exec_block(b, state),
            Terminator::Branch { ref cond, then_blk, else_blk } => {
                let cond = cond.clone();
                let c = self.term_of_operand(&cond, &state);
                // then-branch assumes cond, else-branch assumes !cond.
                let mut then_state = state.clone();
                then_state.path = then_state.path.and(Prop::Holds(c.clone()));
                self.exec_block(then_blk, then_state);

                let mut else_state = state;
                else_state.path = else_state.path.and(Prop::Holds(Term::un(UnOp::Not, c)));
                self.exec_block(else_blk, else_state);
            }
            Terminator::Match { ref scrutinee, ref arms, otherwise } => {
                // Explore each arm's target as a separate path. The kernel `Term`
                // cannot express a discriminant test, so we add no extra path
                // constraint per arm (keeping it simple, as allowed). We still
                // evaluate the scrutinee so any obligation inside it is emitted.
                let scrutinee = scrutinee.clone();
                let arms = arms.clone();
                let _ = self.term_of_operand(&scrutinee, &state);
                for arm in &arms {
                    self.exec_block(arm.target, state.clone());
                }
                if let Some(other) = otherwise {
                    self.exec_block(other, state);
                }
            }
            Terminator::Return(ref op) => {
                let op = op.clone();
                // POSTCONDITION: prove post[result := returned value] under the path.
                let ret_term = self.term_of_operand(&op, &state);
                let goal = self.subst_result(&self.f.post, &ret_term);
                self.emit(state.path.clone(), goal, "postcondition");
            }
            // PANIC: a `panic` ABORTS — this is a DIVERGING path. It has no
            // successors and does not return, so the function's postcondition need
            // not hold here: we emit NO obligation and simply stop this path.
            //
            // SOUNDNESS: dropping a panicking path's postcondition obligation is
            // sound precisely because such a path never returns a value, so there is
            // nothing for the postcondition to constrain. NOTE: we are NOT proving
            // panic-freedom — reaching a panic is *permitted* and just aborts.
            // Proving panics unreachable would be a strictly stronger future check.
            Terminator::Panic => { /* diverges: stop this path, emit nothing */ }
            Terminator::Drop { next, .. } => self.exec_block(next, state),
        }
    }

    /// The leading `Invariant` propositions of a block, if it is a loop header.
    /// Returns `None` for any block that does not start with an `Invariant`.
    fn loop_invariants(&self, id: BlockId) -> Option<Vec<Prop>> {
        let blk = self.block(id);
        let invs: Vec<Prop> = blk
            .stmts
            .iter()
            .take_while(|s| matches!(s, Stmt::Invariant(_)))
            .map(|s| match s {
                Stmt::Invariant(p) => p.clone(),
                _ => unreachable!(),
            })
            .collect();
        if invs.is_empty() {
            None
        } else {
            Some(invs)
        }
    }

    /// Loop-invariant reasoning for a header block carrying `Stmt::Invariant`s.
    ///
    /// Scheme (simplified but soundness-leaning):
    ///   (a) ENTRY: prove each invariant holds in the *incoming* state (path/env as
    ///       we arrived). Origin: "loop invariant on entry".
    ///   (b) HAVOC + ASSUME: every local assigned anywhere in the loop body is
    ///       replaced by a fresh symbolic variable, and the path is reset to just
    ///       the invariants. This models "the top of an arbitrary iteration: only
    ///       the invariants are known". Parameters not written in the loop keep
    ///       their values (so the invariant can still mention them).
    ///   (c) BODY: execute the body once from past the invariant statements. On the
    ///       back-edge to the header, prove each invariant again ("loop invariant
    ///       preserved") and stop (do not re-enter the header). On the exit edge,
    ///       continue with the invariants assumed (the branch's ¬cond is added by
    ///       the normal `Branch` handling), so post-loop code may use them.
    ///
    /// SOUNDNESS CAVEATS (documented, not worked around):
    ///   * Resetting the path to the invariants alone *drops* entry hypotheses
    ///     (incl. `pre`) that were not re-stated as invariants. This is the
    ///     standard inductive-invariant assumption; a too-weak invariant yields an
    ///     unprovable "preserved"/post obligation, never a false "verified".
    ///   * The loop body is approximated as "every block reachable from the header
    ///     without an intervening Return". Assigned-local detection is syntactic.
    ///   * Only a single symbolic iteration is explored; nested loops are handled
    ///     by recursion (an inner header re-triggers this scheme).
    fn exec_loop_header(&mut self, header: BlockId, state: State) {
        let invs = self.loop_invariants(header).expect("called on a loop header");

        // (a) ENTRY: each invariant must hold on the way in.
        for inv in &invs {
            let goal = self.resolve_names(inv, &state);
            self.emit(state.path.clone(), goal, "loop invariant on entry");
        }

        // Compute the loop body (header + blocks reachable before a Return) and the
        // set of locals it assigns.
        let body = self.loop_body_blocks(header);
        let assigned = self.assigned_locals(&body);

        // (b) HAVOC: fresh var for every assigned local; reset the path to True and
        // then assume the invariants (resolved against the *havoc'd* env).
        let mut body_state = state;
        body_state.path = Prop::True;
        for local in &assigned {
            let fresh = Term::Var(self.fresh_var("$havoc"));
            body_state.env.insert(*local, fresh);
        }
        for inv in &invs {
            let assumed = self.resolve_names(inv, &body_state);
            body_state.path = body_state.path.clone().and(assumed);
        }

        // Mark the header visited so the back-edge that returns here stops (and the
        // "preserved" obligation is emitted there). We carry the header's
        // invariants in the state so the back-edge can find them.
        body_state.visited.insert(header);
        body_state.loop_headers.insert(header, invs.clone());

        // (c) Execute the header's statements (skipping the invariants, which are
        // no-ops in `exec_stmt`) and then its terminator, exploring the body once.
        let stmts = self.block(header).stmts.clone();
        for stmt in &stmts {
            self.exec_stmt(stmt, &mut body_state);
        }
        self.exec_terminator(header, body_state);
    }

    /// Blocks belonging to a loop body: the header plus everything reachable from
    /// it that can transitively reach the header again (i.e. is "inside" the loop),
    /// bounded by the function's blocks. We approximate with forward reachability
    /// from the header that does not pass through a `Return`, which is adequate for
    /// the structured loops this slice produces.
    fn loop_body_blocks(&self, header: BlockId) -> HashSet<BlockId> {
        let mut body = HashSet::new();
        let mut stack = vec![header];
        while let Some(id) = stack.pop() {
            if !body.insert(id) {
                continue;
            }
            for succ in self.successors(id) {
                // The back-edge to the header is part of the loop but we don't
                // recurse past it (its body is already being collected).
                if succ == header {
                    continue;
                }
                stack.push(succ);
            }
        }
        body
    }

    /// The successor blocks of a block's terminator.
    fn successors(&self, id: BlockId) -> Vec<BlockId> {
        match &self.block(id).term {
            Terminator::Goto(b) => vec![*b],
            Terminator::Branch { then_blk, else_blk, .. } => vec![*then_blk, *else_blk],
            Terminator::Match { arms, otherwise, .. } => {
                let mut v: Vec<BlockId> = arms.iter().map(|a| a.target).collect();
                v.extend(otherwise.iter().copied());
                v
            }
            // A Return ends the path: no successors (this bounds the body search).
            Terminator::Return(_) => vec![],
            // A Panic aborts: no successors (also bounds the body search).
            Terminator::Panic => vec![],
            Terminator::Drop { next, .. } => vec![*next],
        }
    }

    /// The set of locals assigned (whole-local or via a projection) anywhere in the
    /// given blocks. Used to havoc the loop's mutated state.
    ///
    /// A store *through a reference* (`*r = e`) names `r` as its `place.local`, but
    /// the location it actually mutates is `r`'s pointee. Since points-to is
    /// path-sensitive and this scan is static, we cannot know which pointee, so we
    /// over-approximate: if the body contains any deref-store, we also havoc every
    /// local whose address is taken by a `&`/`&mut` in the body (any possible
    /// pointee). This keeps the loop havoc sound in the presence of the strong
    /// updates that [`exec_stmt`] performs through tracked references.
    fn assigned_locals(&self, blocks: &HashSet<BlockId>) -> HashSet<LocalId> {
        let mut out = HashSet::new();
        let mut borrowed_pointees = HashSet::new();
        let mut has_deref_store = false;
        for blk in &self.f.blocks {
            if !blocks.contains(&blk.id) {
                continue;
            }
            for stmt in &blk.stmts {
                if let Stmt::Assign(place, rv) = stmt {
                    out.insert(place.local);
                    if place.proj.iter().any(|p| matches!(p, Proj::Deref)) {
                        has_deref_store = true;
                    }
                    if let RValue::Ref(_, pointee) = rv {
                        borrowed_pointees.insert(pointee.local);
                    }
                }
            }
        }
        if has_deref_store {
            out.extend(borrowed_pointees);
        }
        out
    }

    /// Execute one statement, emitting any obligation it triggers and updating state.
    fn exec_stmt(&mut self, stmt: &Stmt, state: &mut State) {
        match stmt {
            Stmt::Assign(place, rv) => {
                // Emit rvalue-level obligations (division safety, call precondition)
                // *before* binding the result.
                let value = self.term_of_rvalue(rv, state);
                // A write through `a[i] = ..` must prove the index in bounds.
                self.emit_index_bounds(place, state);
                if place.proj.is_empty() {
                    // Whole-local assignment: bind the local to the rvalue term.
                    // A sized-integer local additionally carries its range fact —
                    // its value is in range because every producer (param, checked
                    // op, wrapping op, literal) guarantees it.
                    if let Ty::IntN(w) = self.low.locals[place.local.0 as usize].ty {
                        state.path = range_assumption(std::mem::replace(&mut state.path, Prop::True), &value, w);
                    }
                    state.env.insert(place.local, value);
                    // Track (or invalidate) a points-to fact for this local. `r = &x`
                    // / `r = &mut x` with a bare pointee records `r ↦ x`; any other
                    // rvalue overwrites `r`, so a prior points-to fact is dropped.
                    match rv {
                        RValue::Ref(_, pointee) if pointee.proj.is_empty() => {
                            state.points_to.insert(place.local, pointee.local);
                        }
                        _ => {
                            state.points_to.remove(&place.local);
                        }
                    }
                } else if let ([Proj::Deref], Some(&pointee)) =
                    (place.proj.as_slice(), state.points_to.get(&place.local))
                {
                    // STRONG UPDATE THROUGH A UNIQUE REFERENCE (`*r = e` where we
                    // recorded `r ↦ x`). Because a live `&mut x` is unique (borrow
                    // checker), this store changes exactly the pointee `x`: bind `x`
                    // to the stored value, exactly as a direct `x = e` would. This is
                    // what lets a spec observe mutation through a reference (e.g.
                    // prove `x == 5` after `*r = 5`). Carry the `IntN` range fact too.
                    if let Ty::IntN(w) = self.low.locals[pointee.0 as usize].ty {
                        state.path = range_assumption(std::mem::replace(&mut state.path, Prop::True), &value, w);
                    }
                    state.env.insert(pointee, value);
                } else if place.proj.iter().any(|p| matches!(p, Proj::Deref)) {
                    // STORE THROUGH AN UNTRACKED REFERENCE (`*r = e` where `r`'s
                    // pointee is unknown — a ref parameter, a reborrow, or a store
                    // with further projections like `(*r).f = e`). The write lands on
                    // a pointee we model as opaque, so it changes nothing we know and
                    // we do *nothing*.
                    //
                    // SOUNDNESS: we assert no fact about an untracked pointee, so a
                    // store through a possibly-aliasing reference cannot invalidate a
                    // fact we rely on — there is none. We still evaluated `value`
                    // above, so an obligation inside the stored expression (e.g. a
                    // division) is still emitted.
                    let _ = value;
                } else {
                    // Write *into* a component of an ADT local (`Field`/`Downcast`,
                    // no `Deref`). We cannot represent the updated aggregate in the
                    // kernel `Term`, so we havoc the local to a fresh opaque var
                    // (forgetting any prior fact about it). Sound: we only lose
                    // provability, never gain it.
                    let fresh = Term::Var(self.fresh_var("$agg_upd"));
                    state.env.insert(place.local, fresh);
                }
            }
            Stmt::Assert(p) => {
                // ASSERT: prove `p` under the current path. The assertion is written
                // in terms of source variable *names*; resolve each named local to its
                // current symbolic value so e.g. `assert b != 0` with `b = 2` becomes
                // the goal `2 != 0`.
                let goal = self.resolve_names(p, state);
                self.emit(state.path.clone(), goal, "assert");
            }
            Stmt::Assume(p) => {
                let assumed = self.resolve_names(p, state);
                state.path = state.path.clone().and(assumed);
            }
            // Loop invariants are handled structurally by `exec_block` when it
            // recognizes a loop header (see the loop-invariant scheme there).
            // Reaching one during ordinary statement execution means we are walking
            // *past* the header into the body, where the invariant is already in
            // the (havoc'd) path hypotheses — so there is nothing to do here.
            Stmt::Invariant(_) => {}
        }
    }

    /// Convert an `RValue` to a `Term`, emitting its obligations and (for calls)
    /// assuming the callee postcondition into the path.
    fn term_of_rvalue(&mut self, rv: &RValue, state: &mut State) -> Term {
        match rv {
            RValue::Use(op) => self.term_of_operand(op, state),
            RValue::Bin(op, a, b) => {
                let ta = self.term_of_operand(a, state);
                let tb = self.term_of_operand(b, state);
                // Float arithmetic carries no integer obligations (floats are opaque, no
                // division-by-zero / overflow checks in the linear-integer logic).
                let is_float = matches!(self.operand_ty(a), Ty::Float)
                    || matches!(self.operand_ty(b), Ty::Float);
                // DIVISION SAFETY: divisor must be non-zero.
                if !is_float && matches!(op, BinOp::Div | BinOp::Mod) {
                    let nonzero = Prop::Holds(Term::bin(BinOp::Ne, tb.clone(), Term::Int(0)));
                    self.emit(state.path.clone(), nonzero, "division by zero");
                }
                // OVERFLOW SAFETY: a checked `+`/`-`/`*` result must stay within
                // its integer type's range (width-specific for `IntN`). The
                // `wrapping_*` opt-out (RValue::WrappingBin) skips this.
                if !is_float && matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
                    let (lo, hi) = self.overflow_range(a, b);
                    self.emit_overflow(&Term::bin(*op, ta.clone(), tb.clone()), lo, hi, state);
                }
                Term::bin(*op, ta, tb)
            }
            // Wrapping arithmetic: same value term, but NO overflow obligation.
            RValue::WrappingBin(op, a, b) => {
                let ta = self.term_of_operand(a, state);
                let tb = self.term_of_operand(b, state);
                if matches!(op, BinOp::Div | BinOp::Mod) {
                    let nonzero = Prop::Holds(Term::bin(BinOp::Ne, tb.clone(), Term::Int(0)));
                    self.emit(state.path.clone(), nonzero, "division by zero");
                }
                Term::bin(*op, ta, tb)
            }
            RValue::Un(op, a) => Term::un(*op, self.term_of_operand(a, state)),
            // `v.len()` is modeled as an uninterpreted length term over the
            // vector value — the SAME term the index-bounds check uses, so a guard
            // like `if i < v.len()` discharges `v[i]`'s bound by congruence.
            RValue::VecLen(op) => {
                let t = self.term_of_operand(op, state);
                self.vec_len_term(&t)
            }
            // `push` grows the vector: its value (and hence its length) changes, so
            // we model the result as a fresh opaque vector — no stale length fact
            // survives a push. Operands are still evaluated for their obligations.
            RValue::VecPush(v, x) => {
                let _ = self.term_of_operand(v, state);
                let _ = self.term_of_operand(x, state);
                Term::Var(self.fresh_var("$vec"))
            }
            RValue::Call(callee, args) => {
                let mut arg_terms: Vec<Term> = Vec::with_capacity(args.len());
                for a in args {
                    arg_terms.push(self.term_of_operand(a, state));
                }
                // Fresh symbolic variable for the call's result.
                let r = self.fresh_var("$call_result");

                if let Some(sig) = self.sigs.get(callee) {
                    // CALL PRECONDITION: prove pre[params := args] under the path.
                    let pre = subst_params(&sig.pre, &sig.param_syms, &arg_terms);
                    let origin = format!("precondition of {}", self.syms.resolve(*callee));
                    self.obligations.push(rv_logic::Obligation::new(
                        state.path.clone(),
                        pre,
                        origin,
                    ));

                    // Assume the callee postcondition about `r`: post[params:=args,
                    // result:=r], added to the path.
                    let mut post = subst_params(&sig.post, &sig.param_syms, &arg_terms);
                    post = self.subst_result(&post, &Term::Var(r));
                    state.path = state.path.clone().and(post);
                }
                Term::Var(r)
            }
            // CLOSURE VALUE: opaque to the first-order kernel (no function sort), so a
            // `|args| body` value is a single FRESH opaque variable — exactly like an
            // aggregate. Captured operands are still evaluated for their obligations.
            RValue::Closure(_func, captures) => {
                for c in captures {
                    let _ = self.term_of_operand(c, state);
                }
                Term::Var(self.fresh_var("$closure"))
            }
            // INDIRECT CALL: the target is not statically known, so — like a call to a
            // function with no known signature — the result is a fresh UNCONSTRAINED
            // variable. Sound (nothing false is assumed); imprecise (no contract is
            // applied). Arguments are still evaluated for their obligations.
            RValue::CallClosure(callee, args) => {
                let _ = self.term_of_operand(callee, state);
                for a in args {
                    let _ = self.term_of_operand(a, state);
                }
                Term::Var(self.fresh_var("$call_result"))
            }
            // AGGREGATE: the kernel `Term` has no ADT constructors, so a struct /
            // enum-variant value is modeled as a single FRESH opaque variable.
            // Field operands are still evaluated (so e.g. a division inside a
            // field expression still emits its safety obligation), but the
            // resulting ADT is opaque. This is sound: facts about the ADT's
            // internals simply remain unprovable for this slice.
            RValue::Aggregate(_kind, operands) => {
                for op in operands {
                    let _ = self.term_of_operand(op, state);
                }
                Term::Var(self.fresh_var("$agg"))
            }
            // REFERENCE VALUE: a reference is opaque to the first-order kernel `Term`
            // (it has no pointer/address sort). So `&place` / `&mut place` is modeled
            // as a single FRESH opaque variable. We still evaluate any obligation
            // reachable while forming the place (a projected place is itself opaque,
            // so there is nothing extra to emit here). Sound: nothing is assumed about
            // the reference, so no false obligation can be discharged from it.
            RValue::Ref(_kind, _place) => Term::Var(self.fresh_var("$ref")),
        }
    }

    /// Convert an operand to a term against the current env.
    ///
    /// A single `Field` projection off a base whose symbolic value we know is
    /// modeled as an *uninterpreted projection* [`Term::Field`] — the exact term
    /// the spec lowering builds for `base.field`. Because both sides share the
    /// term, a precondition like `requires p.v != 0` connects (by congruence over
    /// the opaque projection) to a body's read of `p.v`, e.g. a division by it.
    /// This is sound: while the base is unmutated, the same field of the same
    /// value reads equal; a field *write* havocs the base local to a fresh var,
    /// which makes the new projection a distinct term (no stale fact survives).
    ///
    /// Any other projected read (`Deref`, `Downcast`, nested projections, or an
    /// unknown base) stays a FRESH opaque variable: nothing is known about it,
    /// which is sound. A projection-free `Copy` resolves to the local's value.
    fn term_of_operand(&mut self, op: &Operand, state: &State) -> Term {
        // A read through `a[i]` must prove the index in bounds.
        if let Operand::Copy(place) = op {
            self.emit_index_bounds(place, state);
        }
        match op {
            Operand::Const(Const::Int(n)) => Term::Int(*n),
            Operand::Const(Const::Bool(b)) => Term::Bool(*b),
            Operand::Const(Const::Unit) => Term::Int(0),
            // Floats/strings are opaque to the linear solver: a fresh variable, so no two
            // literals are provably equal (sound: never proves a false fact about them).
            Operand::Const(Const::Float(_)) => Term::Var(self.fresh_var("$float")),
            Operand::Const(Const::Str(_)) => Term::Var(self.fresh_var("$str")),
            Operand::Copy(place) if !place.proj.is_empty() => {
                if let [Proj::Field(n)] = place.proj.as_slice() {
                    if let Some(base) = state.env.get(&place.local).cloned() {
                        return Term::field(base, *n);
                    }
                }
                // A read `*r` through a tracked reference (`r ↦ x`) resolves to the
                // pointee's current symbolic value — the same term a direct read of
                // `x` produces, so a fact about `x` connects (by shared term) to a
                // use of `*r`. Sound: while `r` is a live borrow of `x`, `x` is not
                // independently mutated (borrow checker), so its value is stable.
                if let [Proj::Deref] = place.proj.as_slice() {
                    if let Some(&pointee) = state.points_to.get(&place.local) {
                        return state
                            .env
                            .get(&pointee)
                            .cloned()
                            .unwrap_or_else(|| Term::Var(self.local_sym(&Place::local(pointee))));
                    }
                }
                Term::Var(self.fresh_var("$proj"))
            }
            Operand::Copy(place) => state
                .env
                .get(&place.local)
                .cloned()
                .unwrap_or_else(|| Term::Var(self.local_sym(place))),
        }
    }

    /// A best-effort symbol for an un-bound local (e.g. a havoc'd / unassigned
    /// local). Uses the declared name if any, else a synthetic id.
    fn local_sym(&self, place: &Place) -> Sym {
        self.f.locals[place.local.0 as usize].name.unwrap_or(Sym(u32::MAX - place.local.0))
    }

    /// Replace each named local in `p` with its current symbolic value from `env`.
    /// Assertions/assumes are written against source names; this bridges them to the
    /// symbolic state. Parameters map to their own name-variable, so they are
    /// unaffected (`Var(p) := Var(p)`).
    fn resolve_names(&self, p: &Prop, state: &State) -> Prop {
        let mut out = p.clone();
        for (local, term) in &state.env {
            if let Some(name) = self.f.locals[local.0 as usize].name {
                out = rv_core::subst_prop(&out, name, term);
            }
        }
        out
    }

    /// Substitute the reserved `result` symbol with `value` in `p`.
    fn subst_result(&mut self, p: &Prop, value: &Term) -> Prop {
        let result = self.syms.intern(RESULT_NAME);
        rv_core::subst_prop(p, result, value)
    }

    /// The length term of a vector value. When the value is a plain symbolic
    /// variable (the common case — a vector local), the length is a deterministic
    /// *linear* variable derived from it, so `v.len()` in a guard and the `v[i]`
    /// bound share one variable the arithmetic solver can reason over. A
    /// non-variable vector value yields a fresh opaque length (sound, but not
    /// guard-connectable). A `push` rebinds the vector to a new variable, which
    /// derives a new — correctly disconnected — length.
    fn vec_len_term(&mut self, vec: &Term) -> Term {
        match vec {
            Term::Var(s) => {
                let base = self.syms.resolve(*s).to_string();
                Term::Var(self.syms.intern(&format!("$len#{base}")))
            }
            _ => Term::Var(self.fresh_var("$len")),
        }
    }

    /// Mint a fresh, unique symbolic variable.
    fn fresh_var(&mut self, base: &str) -> Sym {
        // The interner dedups, so a process-global uniquifier keeps names distinct.
        let unique = format!("{base}#{}", fresh_counter());
        self.syms.intern(&unique)
    }

    /// Push an obligation with the given hypotheses, goal, and origin.
    fn emit(&mut self, ctx: Prop, goal: Prop, origin: &str) {
        self.obligations.push(rv_logic::Obligation::new(ctx, goal, origin));
    }

    /// For each `Proj::Index(i)` in `place`, emit the bounds obligation
    /// `0 <= i < len`. For a fixed `[T; N]` array the upper bound is the static
    /// length `N`; for a `Vec<T>` it is the *symbolic* length term `len(v)` (the
    /// same term `v.len()` produces, so a `if i < v.len()` guard discharges it).
    /// A non-indexable / unresolved base emits nothing — sound, since an
    /// out-of-bounds access just stays unproven elsewhere.
    fn emit_index_bounds(&mut self, place: &Place, state: &State) {
        if !place.proj.iter().any(|p| matches!(p, Proj::Index(_))) {
            return;
        }
        let base = self.low.locals[place.local.0 as usize].ty.clone();
        for (i, p) in place.proj.iter().enumerate() {
            let Proj::Index(idx_op) = p else { continue };
            // The upper bound depends on whether the indexed value is a static
            // array (constant length) or a growable vector (symbolic length).
            let upper = match resolve_proj_ty(&base, &place.proj[..i], self.types) {
                Ty::Array(_, len) => Term::Int(len as i64),
                Ty::Vec(_) => {
                    let bt = self.place_prefix_term(place, i, state);
                    self.vec_len_term(&bt)
                }
                _ => continue,
            };
            let idx = self.term_of_operand(idx_op, state);
            let lo = Prop::Holds(Term::bin(BinOp::Ge, idx.clone(), Term::Int(0)));
            let hi = Prop::Holds(Term::bin(BinOp::Lt, idx, upper));
            self.emit(state.path.clone(), lo, "index out of bounds (negative)");
            self.emit(state.path.clone(), hi, "index out of bounds");
        }
    }

    /// The symbolic term of the place `place.local` followed by its first `upto`
    /// projections. Used to name a vector value when forming its `len(v)` bound.
    /// Only the common direct-local case (`upto == 0`) is resolved precisely; a
    /// deeper prefix yields a fresh opaque term (sound, just not guard-connectable).
    fn place_prefix_term(&mut self, place: &Place, upto: usize, state: &State) -> Term {
        if upto == 0 {
            return state.env.get(&place.local).cloned().unwrap_or_else(|| {
                Term::Var(self.f.locals[place.local.0 as usize].name.unwrap_or(Sym(u32::MAX - place.local.0)))
            });
        }
        Term::Var(self.fresh_var("$vecbase"))
    }

    /// Emit the checked-arithmetic overflow obligation: `result` must lie within
    /// `[lo, hi]` — the range of its integer type (the machine `i64` range for the
    /// default `Int`, or the width-specific range for a sized `IntN`). The
    /// linear-arithmetic solver discharges this whenever the operands are bounded
    /// enough (a `requires`, an `IntN` width, a guard); an unbounded `x + y`
    /// correctly fails to prove.
    fn emit_overflow(&mut self, result: &Term, lo: i64, hi: i64, state: &State) {
        let lo_p = Prop::Holds(Term::bin(BinOp::Ge, result.clone(), Term::Int(lo)));
        let hi_p = Prop::Holds(Term::bin(BinOp::Le, result.clone(), Term::Int(hi)));
        self.emit(state.path.clone(), lo_p, "arithmetic overflow (underflow)");
        self.emit(state.path.clone(), hi_p, "arithmetic overflow");
    }

    /// The type of an operand, resolved from the typed (Lowerable) locals.
    fn operand_ty(&self, op: &Operand) -> Ty {
        match op {
            Operand::Const(Const::Int(_)) => Ty::Int,
            Operand::Const(Const::Float(_)) => Ty::Float,
            Operand::Const(Const::Str(_)) => Ty::Str,
            Operand::Const(Const::Bool(_)) => Ty::Bool,
            Operand::Const(Const::Unit) => Ty::Unit,
            Operand::Copy(place) => {
                let base = self.low.locals[place.local.0 as usize].ty.clone();
                resolve_proj_ty(&base, &place.proj, self.types)
            }
        }
    }

    /// The `[lo, hi]` overflow range for an arithmetic result on `a`/`b`: the
    /// sized-integer width's range when either operand is `IntN`, else the
    /// default machine `i64` range.
    fn overflow_range(&self, a: &Operand, b: &Operand) -> (i64, i64) {
        match int_result_ty(&self.operand_ty(a), &self.operand_ty(b)) {
            Some(Ty::IntN(w)) => (w.min() as i64, w.max() as i64),
            _ => (i64::MIN, i64::MAX),
        }
    }
}

/// Substitute a function's parameter symbols with the corresponding argument terms.
fn subst_params(p: &Prop, params: &[Sym], args: &[Term]) -> Prop {
    let mut out = p.clone();
    for (sym, arg) in params.iter().zip(args.iter()) {
        out = rv_core::subst_prop(&out, *sym, arg);
    }
    out
}

/// A process-global counter so distinct fresh vars never collide.
fn fresh_counter() -> u64 {
    use std::sync::atomic::{AtomicU64, Ordering};
    static N: AtomicU64 = AtomicU64::new(0);
    N.fetch_add(1, Ordering::Relaxed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rv_ir::LocalDecl;

    /// Helper: a one-block function with the given statements and terminator.
    fn func(
        name: Sym,
        params: Vec<LocalId>,
        locals: Vec<LocalDecl<Parsed>>,
        pre: Prop,
        post: Prop,
        stmts: Vec<Stmt>,
        term: Terminator<Parsed>,
    ) -> Function<Parsed> {
        Function {
            name,
            type_params: vec![],
            params,
            ret: None,
            pre,
            post,
            locals,
            blocks: vec![Block { id: BlockId(0), stmts, term }],
            entry: BlockId(0),
        }
    }

    fn decl(name: Option<Sym>) -> LocalDecl<Parsed> {
        LocalDecl { name, ty: None }
    }

    /// (a) Elaboration produces a `Lowerable` program and infers types.
    #[test]
    fn elaborates_to_lowerable_with_types() {
        let mut syms = Symbols::new();
        let f = syms.intern("f");
        // local 0 = 1 + 2 (Int). One block: l0 = 1 + 2; return l0.
        let l0 = LocalId(0);
        let prog = Program {
            types: vec![],
            funcs: vec![func(
                f,
                vec![],
                vec![decl(None)],
                Prop::True,
                Prop::True,
                vec![Stmt::Assign(
                    Place::local(l0),
                    RValue::Bin(
                        BinOp::Add,
                        Operand::Const(Const::Int(1)),
                        Operand::Const(Const::Int(2)),
                    ),
                )],
                Terminator::Return(Operand::Copy(Place::local(l0))),
            )],
        };
        let elab = elaborate(prog, &syms).expect("elaboration");
        // The output program is in the Lowerable phase with real types.
        assert_eq!(elab.prog.funcs[0].ret, Ty::Int);
        assert_eq!(elab.prog.funcs[0].locals[0].ty, Ty::Int);
    }

    /// A type error (adding a bool) is rejected.
    #[test]
    fn rejects_adding_a_bool() {
        let mut syms = Symbols::new();
        let f = syms.intern("bad");
        let l0 = LocalId(0);
        let prog = Program {
            types: vec![],
            funcs: vec![func(
                f,
                vec![],
                vec![decl(None)],
                Prop::True,
                Prop::True,
                vec![Stmt::Assign(
                    Place::local(l0),
                    RValue::Bin(
                        BinOp::Add,
                        Operand::Const(Const::Bool(true)),
                        Operand::Const(Const::Int(1)),
                    ),
                )],
                Terminator::Return(Operand::Copy(Place::local(l0))),
            )],
        };
        assert!(elaborate(prog, &syms).is_err());
    }

    /// (b) A division produces a `!= 0` obligation.
    #[test]
    fn division_emits_nonzero_obligation() {
        let mut syms = Symbols::new();
        let f = syms.intern("g");
        let l0 = LocalId(0);
        let prog = Program {
            types: vec![],
            funcs: vec![func(
                f,
                vec![],
                vec![decl(None)],
                Prop::True,
                Prop::True,
                vec![Stmt::Assign(
                    Place::local(l0),
                    RValue::Bin(
                        BinOp::Div,
                        Operand::Const(Const::Int(6)),
                        Operand::Const(Const::Int(2)),
                    ),
                )],
                Terminator::Return(Operand::Copy(Place::local(l0))),
            )],
        };
        let elab = elaborate(prog, &syms).expect("elaboration");
        let div = elab
            .obligations
            .iter()
            .find(|o| o.origin == "division by zero")
            .expect("a division-by-zero obligation");
        // goal is `divisor != 0`.
        let expected = Prop::Holds(Term::bin(BinOp::Ne, Term::Int(2), Term::Int(0)));
        assert_eq!(div.goal, expected);
    }

    /// (c) A call produces a precondition obligation (with params substituted).
    #[test]
    fn call_emits_precondition_obligation() {
        let mut syms = Symbols::new();
        let callee = syms.intern("callee");
        let caller = syms.intern("caller");
        let x = syms.intern("x");

        // callee(x) requires x > 0, ensures result == x.
        let pre = Prop::Holds(Term::bin(BinOp::Gt, Term::Var(x), Term::Int(0)));
        let result_sym = syms.intern(RESULT_NAME);
        let post = Prop::Holds(Term::bin(BinOp::Eq, Term::Var(result_sym), Term::Var(x)));
        let l_x = LocalId(0);
        let callee_fn = func(
            callee,
            vec![l_x],
            vec![decl(Some(x))],
            pre,
            post,
            vec![],
            Terminator::Return(Operand::Copy(Place::local(l_x))),
        );

        // caller(): t = callee(5); return t.
        let l_t = LocalId(0);
        let caller_fn = func(
            caller,
            vec![],
            vec![decl(None)],
            Prop::True,
            Prop::True,
            vec![Stmt::Assign(
                Place::local(l_t),
                RValue::Call(callee, vec![Operand::Const(Const::Int(5))]),
            )],
            Terminator::Return(Operand::Copy(Place::local(l_t))),
        );

        let prog = Program { types: vec![], funcs: vec![callee_fn, caller_fn] };
        let elab = elaborate(prog, &syms).expect("elaboration");
        let pre_ob = elab
            .obligations
            .iter()
            .find(|o| o.origin == "precondition of callee")
            .expect("a precondition obligation");
        // pre[x := 5]  ==>  5 > 0
        let expected = Prop::Holds(Term::bin(BinOp::Gt, Term::Int(5), Term::Int(0)));
        assert_eq!(pre_ob.goal, expected);
    }

    // -- ADT / match / loop tests -------------------------------------------

    use rv_ir::{AggKind, FieldDef, MatchArm, TypeDef, VariantDef};

    /// Helper: a multi-block function (blocks given explicitly).
    fn func_blocks(
        name: Sym,
        params: Vec<LocalId>,
        locals: Vec<LocalDecl<Parsed>>,
        pre: Prop,
        post: Prop,
        blocks: Vec<Block<Parsed>>,
    ) -> Function<Parsed> {
        let entry = blocks[0].id;
        Function { name, type_params: vec![], params, ret: None, pre, post, locals, blocks, entry }
    }

    /// A two-variant enum `E { A, B }` as a `TypeDef`.
    fn two_variant_enum(syms: &mut Symbols) -> (Sym, TypeDef) {
        let e = syms.intern("E");
        let a = syms.intern("A");
        let b = syms.intern("B");
        let td = TypeDef::Enum {
            name: e,
            type_params: vec![],
            variants: vec![
                VariantDef { name: a, fields: vec![] },
                VariantDef { name: b, fields: vec![] },
            ],
        };
        (e, td)
    }

    /// (a) A match covering all variants elaborates successfully.
    #[test]
    fn exhaustive_match_elaborates() {
        let mut syms = Symbols::new();
        let (e, enum_td) = two_variant_enum(&mut syms);
        let f = syms.intern("m");

        // local 0 : E (scrutinee, built as variant 0 of E). locals 1 used for returns.
        let l_s = LocalId(0);

        // b0: s = E::A; match s { 0 => b1, 1 => b2 }   (no otherwise)
        let b0 = Block {
            id: BlockId(0),
            stmts: vec![Stmt::Assign(
                Place::local(l_s),
                RValue::Aggregate(AggKind::Variant(e, 0), vec![]),
            )],
            term: Terminator::Match {
                scrutinee: Operand::Copy(Place::local(l_s)),
                arms: vec![
                    MatchArm { variant: 0, target: BlockId(1) },
                    MatchArm { variant: 1, target: BlockId(2) },
                ],
                otherwise: None,
            },
        };
        let b1 = Block {
            id: BlockId(1),
            stmts: vec![],
            term: Terminator::Return(Operand::Const(Const::Int(1))),
        };
        let b2 = Block {
            id: BlockId(2),
            stmts: vec![],
            term: Terminator::Return(Operand::Const(Const::Int(2))),
        };

        let func = func_blocks(
            f,
            vec![],
            vec![decl(None)],
            Prop::True,
            Prop::True,
            vec![b0, b1, b2],
        );
        let prog = Program { types: vec![enum_td], funcs: vec![func] };
        let elab = elaborate(prog, &syms).expect("exhaustive match should elaborate");
        // The scrutinee local was typed as the ADT.
        assert_eq!(elab.prog.funcs[0].locals[0].ty, Ty::Adt(e));
        // types carried through unchanged.
        assert_eq!(elab.prog.types.len(), 1);
    }

    /// (b) A non-exhaustive match (missing a variant, no `otherwise`) is rejected.
    #[test]
    fn non_exhaustive_match_errs() {
        let mut syms = Symbols::new();
        let (e, enum_td) = two_variant_enum(&mut syms);
        let f = syms.intern("m");
        let l_s = LocalId(0);

        // b0: s = E::A; match s { 0 => b1 }   -- variant 1 uncovered, no otherwise.
        let b0 = Block {
            id: BlockId(0),
            stmts: vec![Stmt::Assign(
                Place::local(l_s),
                RValue::Aggregate(AggKind::Variant(e, 0), vec![]),
            )],
            term: Terminator::Match {
                scrutinee: Operand::Copy(Place::local(l_s)),
                arms: vec![MatchArm { variant: 0, target: BlockId(1) }],
                otherwise: None,
            },
        };
        let b1 = Block {
            id: BlockId(1),
            stmts: vec![],
            term: Terminator::Return(Operand::Const(Const::Int(1))),
        };

        let func =
            func_blocks(f, vec![], vec![decl(None)], Prop::True, Prop::True, vec![b0, b1]);
        let prog = Program { types: vec![enum_td], funcs: vec![func] };
        match elaborate(prog, &syms) {
            Err(e) => assert_eq!(e, "non-exhaustive match"),
            Ok(_) => panic!("non-exhaustive match should error"),
        }
    }

    /// (c) A simple counting loop with an invariant emits the "on entry" and
    /// "preserved" obligations.
    #[test]
    fn loop_invariant_emits_entry_and_preserved() {
        let mut syms = Symbols::new();
        let f = syms.intern("count");
        let i = syms.intern("i");
        // local 0 = i (the counter), named so the invariant can mention it.
        let l_i = LocalId(0);

        // Invariant: i >= 0.
        let inv = Prop::Holds(Term::bin(BinOp::Ge, Term::Var(i), Term::Int(0)));

        // b0 (entry): i = 0; goto header(b1).
        let b0 = Block {
            id: BlockId(0),
            stmts: vec![Stmt::Assign(
                Place::local(l_i),
                RValue::Use(Operand::Const(Const::Int(0))),
            )],
            term: Terminator::Goto(BlockId(1)),
        };
        // b1 (header): invariant i >= 0; branch (i < 10) ? body(b2) : exit(b3).
        let cond = LocalId(1); // a fresh local holding the loop condition value
        let b1 = Block {
            id: BlockId(1),
            stmts: vec![
                Stmt::Invariant(inv.clone()),
                Stmt::Assign(
                    Place::local(cond),
                    RValue::Bin(
                        BinOp::Lt,
                        Operand::Copy(Place::local(l_i)),
                        Operand::Const(Const::Int(10)),
                    ),
                ),
            ],
            term: Terminator::Branch {
                cond: Operand::Copy(Place::local(cond)),
                then_blk: BlockId(2),
                else_blk: BlockId(3),
            },
        };
        // b2 (body): i = i + 1; goto header(b1)  -- the back-edge.
        let b2 = Block {
            id: BlockId(2),
            stmts: vec![Stmt::Assign(
                Place::local(l_i),
                RValue::Bin(
                    BinOp::Add,
                    Operand::Copy(Place::local(l_i)),
                    Operand::Const(Const::Int(1)),
                ),
            )],
            term: Terminator::Goto(BlockId(1)),
        };
        // b3 (exit): return i.
        let b3 = Block {
            id: BlockId(3),
            stmts: vec![],
            term: Terminator::Return(Operand::Copy(Place::local(l_i))),
        };

        let func = func_blocks(
            f,
            vec![],
            vec![decl(Some(i)), decl(None)],
            Prop::True,
            Prop::True,
            vec![b0, b1, b2, b3],
        );
        let prog = Program { types: vec![], funcs: vec![func] };
        let elab = elaborate(prog, &syms).expect("loop elaboration");

        let entry = elab.obligations.iter().any(|o| o.origin == "loop invariant on entry");
        let preserved =
            elab.obligations.iter().any(|o| o.origin == "loop invariant preserved");
        assert!(entry, "expected a 'loop invariant on entry' obligation");
        assert!(preserved, "expected a 'loop invariant preserved' obligation");
    }

    // -- reference tests -----------------------------------------------------

    use rv_ir::BorrowKind;

    /// (a) `&mut x` (with `x: Int`) is typed as `Ref { mutable: true, inner: Int }`.
    #[test]
    fn mut_borrow_typed_as_ref_mut_int() {
        let mut syms = Symbols::new();
        let f = syms.intern("borrow_mut");
        // local 0 = x (an Int, pinned by `x = 7`); local 1 = &mut x.
        let l_x = LocalId(0);
        let l_r = LocalId(1);
        let prog = Program {
            types: vec![],
            funcs: vec![func(
                f,
                vec![],
                vec![decl(None), decl(None)],
                Prop::True,
                Prop::True,
                vec![
                    Stmt::Assign(
                        Place::local(l_x),
                        RValue::Use(Operand::Const(Const::Int(7))),
                    ),
                    Stmt::Assign(
                        Place::local(l_r),
                        RValue::Ref(BorrowKind::Mut, Place::local(l_x)),
                    ),
                ],
                Terminator::Return(Operand::Const(Const::Unit)),
            )],
        };
        let elab = elaborate(prog, &syms).expect("elaboration");
        assert_eq!(elab.prog.funcs[0].locals[0].ty, Ty::Int);
        assert_eq!(
            elab.prog.funcs[0].locals[1].ty,
            Ty::Ref { mutable: true, inner: Box::new(Ty::Int) }
        );
    }

    /// (b) A function taking `&T` (and reading the pointee via `Deref`) elaborates;
    /// the `Deref` projection resolves the pointee type back to `Int`.
    #[test]
    fn fn_taking_shared_ref_elaborates() {
        let mut syms = Symbols::new();
        let f = syms.intern("read_ref");
        let r = syms.intern("r");
        // param 0 = r : &Int (pinned by borrowing an int local first is not needed —
        // here we pin r's type directly via a shared borrow of a fresh int local).
        // Simpler: local 0 = n (Int); local 1 = r = &n; local 2 = *r (reads pointee).
        let l_n = LocalId(0);
        let l_r = LocalId(1);
        let l_v = LocalId(2);
        let deref_place = Place { local: l_r, proj: vec![Proj::Deref] };
        let prog = Program {
            types: vec![],
            funcs: vec![func(
                f,
                vec![],
                vec![decl(None), decl(Some(r)), decl(None)],
                Prop::True,
                Prop::True,
                vec![
                    Stmt::Assign(
                        Place::local(l_n),
                        RValue::Use(Operand::Const(Const::Int(3))),
                    ),
                    Stmt::Assign(
                        Place::local(l_r),
                        RValue::Ref(BorrowKind::Shared, Place::local(l_n)),
                    ),
                    // v = *r : reads through the shared ref (Deref resolves to Int).
                    Stmt::Assign(Place::local(l_v), RValue::Use(Operand::Copy(deref_place))),
                ],
                Terminator::Return(Operand::Const(Const::Unit)),
            )],
        };
        let elab = elaborate(prog, &syms).expect("shared-ref function should elaborate");
        // r is `&Int` (shared).
        assert_eq!(
            elab.prog.funcs[0].locals[1].ty,
            Ty::Ref { mutable: false, inner: Box::new(Ty::Int) }
        );
    }

    /// (c) Borrowing and then storing through a reference (`*r = e`) elaborates and
    /// emits NO obligation about the pointee (stores through a ref are sound no-ops
    /// for the env). The stored expression's own obligations are still emitted.
    #[test]
    fn store_through_ref_no_false_obligation() {
        let mut syms = Symbols::new();
        let f = syms.intern("store_ref");
        // local 0 = x (Int); local 1 = r = &mut x; then *r = 6 / 2 (a store through r).
        let l_x = LocalId(0);
        let l_r = LocalId(1);
        let deref_place = Place { local: l_r, proj: vec![Proj::Deref] };
        let prog = Program {
            types: vec![],
            funcs: vec![func(
                f,
                vec![],
                vec![decl(None), decl(None)],
                Prop::True,
                Prop::True,
                vec![
                    Stmt::Assign(
                        Place::local(l_x),
                        RValue::Use(Operand::Const(Const::Int(0))),
                    ),
                    Stmt::Assign(
                        Place::local(l_r),
                        RValue::Ref(BorrowKind::Mut, Place::local(l_x)),
                    ),
                    // *r = 6 / 2 : store through the ref; should be a sound no-op for
                    // env but still emit the division-safety obligation for `6 / 2`.
                    Stmt::Assign(
                        deref_place,
                        RValue::Bin(
                            BinOp::Div,
                            Operand::Const(Const::Int(6)),
                            Operand::Const(Const::Int(2)),
                        ),
                    ),
                ],
                Terminator::Return(Operand::Const(Const::Unit)),
            )],
        };
        let elab = elaborate(prog, &syms).expect("store-through-ref should elaborate");
        // The division inside the stored expression still emits its safety obligation.
        let div = elab.obligations.iter().any(|o| o.origin == "division by zero");
        assert!(div, "expected the stored expression's division obligation");
        // No obligation should mention a pointee fact — the only goal-bearing
        // obligations here are the division check and the (trivially true) post.
        // Crucially, elaboration succeeded with no false obligation about `x`/`*r`.
        for o in &elab.obligations {
            assert!(
                o.origin == "division by zero" || o.origin == "postcondition",
                "unexpected obligation origin: {}",
                o.origin
            );
        }
    }

    /// (d) STRONG UPDATE: after `r = &mut x; *r = 5`, the verifier knows `x == 5`.
    /// The `assert x == 5` obligation resolves to the trivially-true `5 == 5`,
    /// proving the store through the unique reference updated the pointee's value.
    /// This is the ownership → dependency bridge in action.
    #[test]
    fn strong_update_through_mut_ref_updates_pointee() {
        let mut syms = Symbols::new();
        let f = syms.intern("f");
        let x = syms.intern("x");
        let r = syms.intern("r");
        let l_x = LocalId(0);
        let l_r = LocalId(1);
        let deref = Place { local: l_r, proj: vec![Proj::Deref] };
        let assert_x5 = Prop::Holds(Term::bin(BinOp::Eq, Term::Var(x), Term::Int(5)));
        let prog = Program {
            types: vec![],
            funcs: vec![func(
                f,
                vec![],
                vec![decl(Some(x)), decl(Some(r))],
                Prop::True,
                Prop::True,
                vec![
                    Stmt::Assign(Place::local(l_x), RValue::Use(Operand::Const(Const::Int(1)))),
                    Stmt::Assign(Place::local(l_r), RValue::Ref(BorrowKind::Mut, Place::local(l_x))),
                    Stmt::Assign(deref, RValue::Use(Operand::Const(Const::Int(5)))),
                    Stmt::Assert(assert_x5),
                ],
                Terminator::Return(Operand::Const(Const::Unit)),
            )],
        };
        let elab = elaborate(prog, &syms).expect("elaboration");
        let a = elab.obligations.iter().find(|o| o.origin == "assert").expect("assert obligation");
        // x was strong-updated to 5, so the goal is `5 == 5`.
        assert_eq!(a.goal, Prop::Holds(Term::bin(BinOp::Eq, Term::Int(5), Term::Int(5))));
    }

    /// (e) SOUNDNESS GUARD: without the store, `x` keeps its value `1`, so the same
    /// `assert x == 5` resolves to `1 == 5` — *not* trivially true. Confirms the
    /// strong update reflects the actual stored value rather than always succeeding.
    #[test]
    fn no_store_leaves_pointee_value_unchanged() {
        let mut syms = Symbols::new();
        let f = syms.intern("f");
        let x = syms.intern("x");
        let r = syms.intern("r");
        let l_x = LocalId(0);
        let l_r = LocalId(1);
        let assert_x5 = Prop::Holds(Term::bin(BinOp::Eq, Term::Var(x), Term::Int(5)));
        let prog = Program {
            types: vec![],
            funcs: vec![func(
                f,
                vec![],
                vec![decl(Some(x)), decl(Some(r))],
                Prop::True,
                Prop::True,
                vec![
                    Stmt::Assign(Place::local(l_x), RValue::Use(Operand::Const(Const::Int(1)))),
                    Stmt::Assign(Place::local(l_r), RValue::Ref(BorrowKind::Mut, Place::local(l_x))),
                    Stmt::Assert(assert_x5),
                ],
                Terminator::Return(Operand::Const(Const::Unit)),
            )],
        };
        let elab = elaborate(prog, &syms).expect("elaboration");
        let a = elab.obligations.iter().find(|o| o.origin == "assert").expect("assert obligation");
        // No store: x is still 1, goal is the non-trivial `1 == 5`.
        assert_eq!(a.goal, Prop::Holds(Term::bin(BinOp::Eq, Term::Int(1), Term::Int(5))));
    }

    /// (f) READ THROUGH A REFERENCE: `let n = 7; r = &n; v = *r` binds `v` to the
    /// pointee's value, so `assert v == 7` resolves to `7 == 7`. A shared read now
    /// connects to the borrowed value instead of being opaque.
    #[test]
    fn read_through_shared_ref_sees_pointee_value() {
        let mut syms = Symbols::new();
        let f = syms.intern("f");
        let n = syms.intern("n");
        let r = syms.intern("r");
        let v = syms.intern("v");
        let l_n = LocalId(0);
        let l_r = LocalId(1);
        let l_v = LocalId(2);
        let deref = Place { local: l_r, proj: vec![Proj::Deref] };
        let assert_v7 = Prop::Holds(Term::bin(BinOp::Eq, Term::Var(v), Term::Int(7)));
        let prog = Program {
            types: vec![],
            funcs: vec![func(
                f,
                vec![],
                vec![decl(Some(n)), decl(Some(r)), decl(Some(v))],
                Prop::True,
                Prop::True,
                vec![
                    Stmt::Assign(Place::local(l_n), RValue::Use(Operand::Const(Const::Int(7)))),
                    Stmt::Assign(Place::local(l_r), RValue::Ref(BorrowKind::Shared, Place::local(l_n))),
                    Stmt::Assign(Place::local(l_v), RValue::Use(Operand::Copy(deref))),
                    Stmt::Assert(assert_v7),
                ],
                Terminator::Return(Operand::Const(Const::Unit)),
            )],
        };
        let elab = elaborate(prog, &syms).expect("elaboration");
        let a = elab.obligations.iter().find(|o| o.origin == "assert").expect("assert obligation");
        assert_eq!(a.goal, Prop::Holds(Term::bin(BinOp::Eq, Term::Int(7), Term::Int(7))));
    }

    // -- generics tests ------------------------------------------------------

    /// (a) A generic identity function `fn id<T>(x: T) -> T { return x; }`
    /// elaborates without a type error. `type_params` is carried through the phase
    /// change; the param/return are abstract (in the `Parsed` phase local types are
    /// erased), and returning an opaque value raises no type error.
    #[test]
    fn generic_identity_elaborates() {
        let mut syms = Symbols::new();
        let id = syms.intern("id");
        let t = syms.intern("T");
        let x = syms.intern("x");
        // param 0 = x : T. body: return x.
        let l_x = LocalId(0);
        let mut f = func(
            id,
            vec![l_x],
            vec![decl(Some(x))],
            Prop::True,
            Prop::True,
            vec![],
            Terminator::Return(Operand::Copy(Place::local(l_x))),
        );
        f.type_params = vec![t];

        let prog = Program { types: vec![], funcs: vec![f] };
        let elab = elaborate(prog, &syms).expect("generic identity should elaborate");
        // The type parameter is carried through to the Lowerable program.
        assert_eq!(elab.prog.funcs[0].type_params, vec![t]);
    }

    /// A generic struct whose field is declared `Ty::Param(T)` resolves that field's
    /// type to the opaque `Ty::Param(T)` (kept opaque, not flattened to Int), and
    /// using such a value where arithmetic would normally demand `Int` raises NO type
    /// error — the lenient-but-sound generic path.
    #[test]
    fn generic_param_field_is_opaque_and_lenient() {
        let mut syms = Symbols::new();
        let f = syms.intern("use_box");
        let box_ty = syms.intern("Box");
        let tp = syms.intern("T");
        let val = syms.intern("val");

        // struct Box<T> { val: T }
        let box_def = TypeDef::Struct {
            name: box_ty,
            type_params: vec![tp],
            fields: vec![FieldDef { name: val, ty: Ty::Param(tp) }],
        };

        // local 0 = b : Box<T>  (built by aggregate, so typed Adt(Box)).
        // local 1 = b.val       (a Field projection -> resolves to Param(T)).
        // local 2 = b.val + 1   (arithmetic on a Param operand: must NOT error).
        let l_b = LocalId(0);
        let l_v = LocalId(1);
        let l_s = LocalId(2);
        let field_place = Place { local: l_b, proj: vec![Proj::Field(0)] };
        let blk = Block {
            id: BlockId(0),
            stmts: vec![
                Stmt::Assign(
                    Place::local(l_b),
                    RValue::Aggregate(
                        AggKind::Struct(box_ty),
                        vec![Operand::Const(Const::Int(7))],
                    ),
                ),
                Stmt::Assign(
                    Place::local(l_v),
                    RValue::Use(Operand::Copy(field_place)),
                ),
                Stmt::Assign(
                    Place::local(l_s),
                    RValue::Bin(
                        BinOp::Add,
                        Operand::Copy(Place::local(l_v)),
                        Operand::Const(Const::Int(1)),
                    ),
                ),
            ],
            term: Terminator::Return(Operand::Const(Const::Unit)),
        };
        let func = func_blocks(
            f,
            vec![],
            vec![decl(None), decl(Some(val)), decl(None)],
            Prop::True,
            Prop::True,
            vec![blk],
        );
        let prog = Program { types: vec![box_def], funcs: vec![func] };
        let elab = elaborate(prog, &syms).expect("generic-field use should elaborate leniently");
        // The struct local is typed as its ADT (type arguments erased).
        assert_eq!(elab.prog.funcs[0].locals[0].ty, Ty::Adt(box_ty));
    }

    /// (b) A generic enum `Option<T> { None, Some(T) }` with an exhaustive `match`
    /// elaborates: exhaustiveness uses the variant count from the (generic) `TypeDef`,
    /// which is unaffected by the type parameter.
    #[test]
    fn generic_enum_match_elaborates() {
        let mut syms = Symbols::new();
        let opt = syms.intern("Option");
        let tp = syms.intern("T");
        let none = syms.intern("None");
        let some = syms.intern("Some");
        let m = syms.intern("use_opt");

        // enum Option<T> { None, Some(T) }
        let opt_def = TypeDef::Enum {
            name: opt,
            type_params: vec![tp],
            variants: vec![
                VariantDef { name: none, fields: vec![] },
                VariantDef { name: some, fields: vec![Ty::Param(tp)] },
            ],
        };

        // local 0 : Option<T>, built as None (variant 0).
        let l_s = LocalId(0);
        // b0: s = Option::None; match s { 0 => b1, 1 => b2 }  (exhaustive, no otherwise)
        let b0 = Block {
            id: BlockId(0),
            stmts: vec![Stmt::Assign(
                Place::local(l_s),
                RValue::Aggregate(AggKind::Variant(opt, 0), vec![]),
            )],
            term: Terminator::Match {
                scrutinee: Operand::Copy(Place::local(l_s)),
                arms: vec![
                    MatchArm { variant: 0, target: BlockId(1) },
                    MatchArm { variant: 1, target: BlockId(2) },
                ],
                otherwise: None,
            },
        };
        let b1 = Block {
            id: BlockId(1),
            stmts: vec![],
            term: Terminator::Return(Operand::Const(Const::Int(0))),
        };
        let b2 = Block {
            id: BlockId(2),
            stmts: vec![],
            term: Terminator::Return(Operand::Const(Const::Int(1))),
        };

        let func = func_blocks(
            m,
            vec![],
            vec![decl(None)],
            Prop::True,
            Prop::True,
            vec![b0, b1, b2],
        );
        let prog = Program { types: vec![opt_def], funcs: vec![func] };
        let elab = elaborate(prog, &syms).expect("generic enum match should elaborate");
        // The scrutinee local is typed as the (generic) ADT — type args erased.
        assert_eq!(elab.prog.funcs[0].locals[0].ty, Ty::Adt(opt));

        // A non-exhaustive generic match (drop variant 1) is still rejected.
        let l_s2 = LocalId(0);
        let nb0 = Block {
            id: BlockId(0),
            stmts: vec![Stmt::Assign(
                Place::local(l_s2),
                RValue::Aggregate(AggKind::Variant(opt, 0), vec![]),
            )],
            term: Terminator::Match {
                scrutinee: Operand::Copy(Place::local(l_s2)),
                arms: vec![MatchArm { variant: 0, target: BlockId(1) }],
                otherwise: None,
            },
        };
        let nb1 = Block {
            id: BlockId(1),
            stmts: vec![],
            term: Terminator::Return(Operand::Const(Const::Int(0))),
        };
        let opt_def2 = TypeDef::Enum {
            name: opt,
            type_params: vec![tp],
            variants: vec![
                VariantDef { name: none, fields: vec![] },
                VariantDef { name: some, fields: vec![Ty::Param(tp)] },
            ],
        };
        let nfunc = func_blocks(
            m,
            vec![],
            vec![decl(None)],
            Prop::True,
            Prop::True,
            vec![nb0, nb1],
        );
        let nprog = Program { types: vec![opt_def2], funcs: vec![nfunc] };
        assert!(
            elaborate(nprog, &syms).is_err(),
            "a non-exhaustive generic match must still be rejected"
        );
    }

    // -- panic tests ---------------------------------------------------------

    /// A function that `panic`s on one branch and returns on the other still
    /// elaborates. The panicking path DIVERGES, so it emits NO postcondition
    /// obligation; only the returning path does. We assert exactly one
    /// "postcondition" obligation (from the non-panic side), confirming the
    /// panic arm emitted nothing.
    #[test]
    fn panic_branch_emits_no_postcondition() {
        let mut syms = Symbols::new();
        let f = syms.intern("maybe_panic");
        let p = syms.intern("p");
        let result_sym = syms.intern(RESULT_NAME);

        // param 0 = p : Bool (the branch condition). local 1 = the returned int.
        let l_p = LocalId(0);
        let l_r = LocalId(1);

        // post: result == 1  (a non-trivial postcondition so its obligation is visible).
        let post = Prop::Holds(Term::bin(BinOp::Eq, Term::Var(result_sym), Term::Int(1)));

        // b0 (entry): branch p ? then(b1) : else(b2).
        let b0 = Block {
            id: BlockId(0),
            stmts: vec![],
            term: Terminator::Branch {
                cond: Operand::Copy(Place::local(l_p)),
                then_blk: BlockId(1),
                else_blk: BlockId(2),
            },
        };
        // b1 (then): panic! — diverging, no successors, no postcondition obligation.
        let b1 = Block { id: BlockId(1), stmts: vec![], term: Terminator::Panic };
        // b2 (else): r = 1; return r — emits the (single) postcondition obligation.
        let b2 = Block {
            id: BlockId(2),
            stmts: vec![Stmt::Assign(
                Place::local(l_r),
                RValue::Use(Operand::Const(Const::Int(1))),
            )],
            term: Terminator::Return(Operand::Copy(Place::local(l_r))),
        };

        let func = func_blocks(
            f,
            vec![l_p],
            vec![decl(Some(p)), decl(None)],
            Prop::True,
            post,
            vec![b0, b1, b2],
        );
        let prog = Program { types: vec![], funcs: vec![func] };
        let elab = elaborate(prog, &syms).expect("panic-branch function should elaborate");

        // The Panic terminator is carried through to the Lowerable phase.
        assert!(matches!(elab.prog.funcs[0].blocks[1].term, Terminator::Panic));

        // Exactly one postcondition obligation — from the RETURNING path only. The
        // panicking path diverges and emits nothing.
        let posts = elab.obligations.iter().filter(|o| o.origin == "postcondition").count();
        assert_eq!(posts, 1, "only the non-panic path should emit a postcondition");
    }
}
