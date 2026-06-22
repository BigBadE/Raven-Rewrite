//! Lowering of specification expressions (`requires` / `ensures` / `assert`)
//! into `rv_core` terms and propositions.
//!
//! Spec expressions are *pure*: no calls, no assignments. They mention only
//! parameters / locals (as `Term::Var`) and — inside `ensures` — the reserved
//! `result` identifier, which maps to `Term::Var(intern("result"))`.
//!
//! A spec may also project a field out of a struct-typed variable (`p.v`). Such
//! a field access lowers to an *uninterpreted* [`Term::Field`] — the same term
//! the inference pass builds for a field read in code. Sharing the exact term
//! is what lets the solver connect a precondition `p.v != 0` to a body's
//! division by `p.v` (via congruence over the opaque projection).

use std::collections::HashMap;

use rv_core::{BinOp, Prop, Sym, Symbols, Term, UnOp};
use rv_syntax::ast::Expr;

use crate::types::Types;

/// What a spec expression may refer to beyond bare scalars: the module type
/// registry (for struct field indices) and a map from in-scope variable name to
/// the struct type it has (only struct-typed parameters / `self` are recorded).
pub struct SpecCtx<'a> {
    pub types: &'a Types,
    /// variable name -> struct type name, for resolving `v.field` in a spec.
    pub var_struct: &'a HashMap<Sym, Sym>,
}

/// Lower a boolean spec expression to a [`Prop`].
///
/// Logical connectives (`&&`, `||`, `!`) and comparisons are given structural
/// `Prop` form so the solver sees the logical skeleton; any other boolean-valued
/// term is wrapped in `Prop::Holds`.
pub fn lower_prop(e: &Expr, syms: &mut Symbols, ctx: &SpecCtx) -> Result<Prop, String> {
    match e {
        Expr::Bool(true) => Ok(Prop::True),
        Expr::Bool(false) => Ok(Prop::False),
        Expr::Bin(BinOp::And, a, b) => {
            Ok(lower_prop(a, syms, ctx)?.and(lower_prop(b, syms, ctx)?))
        }
        Expr::Bin(BinOp::Or, a, b) => {
            Ok(lower_prop(a, syms, ctx)?.or(lower_prop(b, syms, ctx)?))
        }
        Expr::Un(UnOp::Not, a) => Ok(lower_prop(a, syms, ctx)?.not()),
        // Comparisons and everything else: lower as a boolean-valued term.
        _ => Ok(Prop::Holds(lower_term(e, syms, ctx)?)),
    }
}

/// Lower a pure spec expression to a [`Term`].
///
/// Rejects constructs that cannot appear in a (first-order) term: calls, the
/// unit literal, aggregates, references, and `?`.
pub fn lower_term(e: &Expr, syms: &mut Symbols, ctx: &SpecCtx) -> Result<Term, String> {
    match e {
        Expr::Int(n) => Ok(Term::Int(*n)),
        Expr::Bool(b) => Ok(Term::Bool(*b)),
        Expr::Var(s) => Ok(Term::Var(*s)),
        Expr::Bin(op, a, b) => Ok(Term::bin(
            *op,
            lower_term(a, syms, ctx)?,
            lower_term(b, syms, ctx)?,
        )),
        Expr::Un(op, a) => Ok(Term::un(*op, lower_term(a, syms, ctx)?)),
        // `v.field` on a struct-typed variable: an uninterpreted projection.
        // The base must be a variable whose struct type we know, so we can map
        // the field name to its index — matching what inference builds in code.
        Expr::Field { base, field } => {
            let base_term = lower_term(base, syms, ctx)?;
            let struct_name = struct_of(base, ctx).ok_or_else(|| {
                format!(
                    "field `{}` in a specification requires a struct-typed variable base",
                    syms.resolve(*field)
                )
            })?;
            let info = ctx.types.struct_info(struct_name).ok_or_else(|| {
                format!("unknown struct `{}` in specification", syms.resolve(struct_name))
            })?;
            let idx = *info.field_index.get(field).ok_or_else(|| {
                format!(
                    "struct `{}` has no field `{}`",
                    syms.resolve(struct_name),
                    syms.resolve(*field)
                )
            })?;
            Ok(Term::field(base_term, idx))
        }
        Expr::Unit => Err("unit `()` is not a valid term in a specification".to_string()),
        Expr::Call { .. } | Expr::MethodCall { .. } => {
            Err("function and method calls are not allowed in specifications".to_string())
        }
        Expr::StructLit { .. } | Expr::EnumCtor { .. } => {
            Err("aggregate values are not allowed in specifications".to_string())
        }
        // References and dereferences are not first-order terms either: the spec
        // logic has no notion of memory / pointees.
        Expr::Ref { .. } | Expr::Deref(_) => {
            Err("references and dereferences are not allowed in specifications".to_string())
        }
        // The `?` operator early-returns / is effectful, so it is not a pure term.
        Expr::Try(_) => {
            Err("the `?` operator is not allowed in specifications".to_string())
        }
        // Floats, strings, and closures are opaque to the first-order spec logic.
        Expr::Float(_) | Expr::Str(_) => {
            Err("float/string literals are not allowed in specifications".to_string())
        }
        Expr::Lambda { .. } => {
            Err("closures are not allowed in specifications".to_string())
        }
        // Proof-fragment expression forms are not first-order spec terms (they route
        // to the kernel, not the spec solver).
        _ => Err("proof-fragment expressions are not allowed in specifications".to_string()),
    }
}

/// The struct type of a spec sub-expression, if statically known. Only a bare
/// variable whose struct type was recorded resolves; deeper bases stay unknown.
fn struct_of(e: &Expr, ctx: &SpecCtx) -> Option<Sym> {
    match e {
        Expr::Var(s) => ctx.var_struct.get(s).copied(),
        _ => None,
    }
}
