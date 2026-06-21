//! The kernel / trust base.
//!
//! Defines the value type system (`Ty`), the pure term language (`Term`), the
//! first-order logic (`Prop`) that verification obligations live in, and a small
//! trusted type-checker. A soundness bug can live *only* here (and in a trusted
//! solver). Keep it small and dependency-light.
//!
//! NOTE: this is the L0 *seed* of `docs/semantic-ir-v3.md`. The design's full
//! QTT + guarded dependent core is future growth; the architecture (kernel as an
//! isolated, minimal, trusted crate) is faithful today.
use rv_arena::Interner;
use std::collections::HashMap;

/// An interned identifier (variable / function name).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct Sym(pub u32);

/// The symbol table. Construct once, thread through parsing/lowering.
#[derive(Debug, Default, Clone)]
pub struct Symbols(Interner<String>);
impl Symbols {
    pub fn new() -> Self {
        Self(Interner::new())
    }
    pub fn intern(&mut self, s: &str) -> Sym {
        Sym(self.0.intern(s.to_string()))
    }
    pub fn resolve(&self, s: Sym) -> &str {
        self.0.resolve(s.0).map(String::as_str).unwrap_or("?")
    }
}

/// A fixed-width integer type: its signedness and bit width. Bounds are computed
/// in `i128` (so every supported width — up to 32-bit unsigned / 64-bit signed —
/// fits without overflow).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct IntTy {
    pub signed: bool,
    pub bits: u8,
}
impl IntTy {
    /// The smallest representable value.
    pub fn min(&self) -> i128 {
        if self.signed {
            -(1i128 << (self.bits - 1))
        } else {
            0
        }
    }
    /// The largest representable value.
    pub fn max(&self) -> i128 {
        if self.signed {
            (1i128 << (self.bits - 1)) - 1
        } else {
            (1i128 << self.bits) - 1
        }
    }
}

/// Value-level types.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Ty {
    Int,
    /// A fixed-width integer (`i8`/`u32`/...). `Int` remains the default unbounded
    /// (i64-range) integer; `IntN` additionally carries a width so the verifier
    /// can emit *width-specific* overflow bounds.
    IntN(IntTy),
    Bool,
    Unit,
    Tuple(Vec<Ty>),
    /// A fixed-size array `[T; n]`: `n` elements of type `T`.
    Array(Box<Ty>, usize),
    /// A growable vector `Vec<T>`. Its length is dynamic, so indexed access is
    /// guarded against a *symbolic* length term rather than a static size.
    Vec(Box<Ty>),
    Fn(Vec<Ty>, Box<Ty>),
    Never,
    /// A user-defined algebraic data type (struct or enum), referenced by name.
    /// Its field/variant structure lives in the IR's `TypeDef` table.
    Adt(Sym),
    /// A reference `&T` (`mutable == false`) or `&mut T` (`mutable == true`).
    Ref { mutable: bool, inner: Box<Ty> },
    /// A generic type parameter (`T` inside `fn f<T>(..)`), opaque to checking.
    Param(Sym),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    /// Bitwise/shift integer operators (`& | ^ << >>`). Their runtime semantics
    /// are exact i64 bit operations; to the linear solver they are *uninterpreted*
    /// (opaque atoms — sound but incomplete: no bit-level reasoning).
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum UnOp {
    Neg,
    Not,
}

/// Pure terms: the spec/expression language that `Prop` is built from.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Term {
    Int(i64),
    Bool(bool),
    Var(Sym),
    Bin(BinOp, Box<Term>, Box<Term>),
    Un(UnOp, Box<Term>),
    /// Uninterpreted projection of a field out of an aggregate term: `base.idx`.
    ///
    /// The kernel treats this as an opaque function symbol — it asserts no
    /// equations about it beyond congruence (equal bases project to equal
    /// fields, supplied by the solver). This keeps the trust base small: a
    /// `Field` term can never make an unsound program verify, only let the
    /// solver connect a spec's `p.v` to the code's read of the same field.
    Field(Box<Term>, u32),
    /// Application of an *uninterpreted function symbol* to arguments:
    /// `f(a0, a1, ...)`. Like [`Term::Field`] it is opaque — the kernel asserts no
    /// equations about `f` beyond **congruence** (equal arguments give equal
    /// results), which the solver supplies. This is the logic-level building block
    /// for sequence reads (`select(seq, i)`), a closure's result (`f(x)` for a
    /// fixed closure), and any other modeled-as-uninterpreted operation. Sound:
    /// an uninterpreted symbol can never make a false goal provable, it only lets
    /// the solver connect two reads of the same function at equal arguments.
    App(Sym, Vec<Term>),
}
impl Term {
    pub fn bin(op: BinOp, a: Term, b: Term) -> Term {
        Term::Bin(op, Box::new(a), Box::new(b))
    }
    pub fn un(op: UnOp, a: Term) -> Term {
        Term::Un(op, Box::new(a))
    }
    pub fn field(base: Term, idx: u32) -> Term {
        Term::Field(Box::new(base), idx)
    }
    pub fn app(f: Sym, args: Vec<Term>) -> Term {
        Term::App(f, args)
    }
}

/// First-order propositions: what obligations are stated in.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Prop {
    True,
    False,
    /// A boolean-valued term (typically a comparison) asserted to hold.
    Holds(Term),
    Not(Box<Prop>),
    And(Box<Prop>, Box<Prop>),
    Or(Box<Prop>, Box<Prop>),
    Implies(Box<Prop>, Box<Prop>),
    Forall(Sym, Box<Prop>),
    Exists(Sym, Box<Prop>),
}
impl Prop {
    pub fn holds(t: Term) -> Prop {
        Prop::Holds(t)
    }
    pub fn and(self, other: Prop) -> Prop {
        match (self, other) {
            (Prop::True, p) | (p, Prop::True) => p,
            (a, b) => Prop::And(Box::new(a), Box::new(b)),
        }
    }
    pub fn or(self, other: Prop) -> Prop {
        Prop::Or(Box::new(self), Box::new(other))
    }
    pub fn implies(self, other: Prop) -> Prop {
        Prop::Implies(Box::new(self), Box::new(other))
    }
    #[allow(clippy::should_implement_trait)]
    pub fn not(self) -> Prop {
        Prop::Not(Box::new(self))
    }
}

/// Typing context: variable -> type.
pub type Ctx = HashMap<Sym, Ty>;

/// The trusted type-checker for terms: returns the term's type or an error message.
pub fn type_of(term: &Term, ctx: &Ctx) -> Result<Ty, String> {
    match term {
        Term::Int(_) => Ok(Ty::Int),
        Term::Bool(_) => Ok(Ty::Bool),
        Term::Var(s) => ctx.get(s).cloned().ok_or_else(|| "unbound variable".to_string()),
        // Field projection is an uninterpreted scalar: we require the base to be
        // well-typed, then assign the projection `Int`. The kernel does not carry
        // an ADT field-type registry, so spec-level field accesses are scalars
        // (the regime in which our first-order solver reasons). This is a typing
        // *restriction*, not a soundness hole — an opaque term cannot prove a
        // false goal.
        Term::Field(base, _) => {
            type_of(base, ctx)?;
            Ok(Ty::Int)
        }
        // An uninterpreted application is a scalar (like `Field`): require every
        // argument to be well-typed, then assign the result `Int`. The kernel
        // reasons about it only through congruence, so the precise result sort is
        // not needed for soundness.
        Term::App(_, args) => {
            for a in args {
                type_of(a, ctx)?;
            }
            Ok(Ty::Int)
        }
        Term::Un(UnOp::Neg, t) => {
            expect(&type_of(t, ctx)?, &Ty::Int)?;
            Ok(Ty::Int)
        }
        Term::Un(UnOp::Not, t) => {
            expect(&type_of(t, ctx)?, &Ty::Bool)?;
            Ok(Ty::Bool)
        }
        Term::Bin(op, a, b) => {
            let (ta, tb) = (type_of(a, ctx)?, type_of(b, ctx)?);
            use BinOp::*;
            match op {
                Add | Sub | Mul | Div | Mod | BitAnd | BitOr | BitXor | Shl | Shr => {
                    expect(&ta, &Ty::Int)?;
                    expect(&tb, &Ty::Int)?;
                    Ok(Ty::Int)
                }
                And | Or => {
                    expect(&ta, &Ty::Bool)?;
                    expect(&tb, &Ty::Bool)?;
                    Ok(Ty::Bool)
                }
                Eq | Ne => {
                    if ta != tb {
                        return Err("type mismatch in (in)equality".to_string());
                    }
                    Ok(Ty::Bool)
                }
                Lt | Le | Gt | Ge => {
                    expect(&ta, &Ty::Int)?;
                    expect(&tb, &Ty::Int)?;
                    Ok(Ty::Bool)
                }
            }
        }
    }
}
fn expect(got: &Ty, want: &Ty) -> Result<(), String> {
    if got == want {
        Ok(())
    } else {
        Err(format!("expected {want:?}, got {got:?}"))
    }
}

/// Substitute `value` for `var` throughout a term.
pub fn subst_term(t: &Term, var: Sym, value: &Term) -> Term {
    match t {
        Term::Var(s) if *s == var => value.clone(),
        Term::Var(_) | Term::Int(_) | Term::Bool(_) => t.clone(),
        Term::Un(op, a) => Term::Un(*op, Box::new(subst_term(a, var, value))),
        Term::Bin(op, a, b) => {
            Term::Bin(*op, Box::new(subst_term(a, var, value)), Box::new(subst_term(b, var, value)))
        }
        Term::Field(base, idx) => Term::Field(Box::new(subst_term(base, var, value)), *idx),
        Term::App(f, args) => {
            Term::App(*f, args.iter().map(|a| subst_term(a, var, value)).collect())
        }
    }
}

/// Substitute `value` for `var` throughout a proposition (capture-avoiding for our
/// closed-term substitutions: we stop at a shadowing binder).
pub fn subst_prop(p: &Prop, var: Sym, value: &Term) -> Prop {
    match p {
        Prop::True | Prop::False => p.clone(),
        Prop::Holds(t) => Prop::Holds(subst_term(t, var, value)),
        Prop::Not(a) => Prop::Not(Box::new(subst_prop(a, var, value))),
        Prop::And(a, b) => {
            Prop::And(Box::new(subst_prop(a, var, value)), Box::new(subst_prop(b, var, value)))
        }
        Prop::Or(a, b) => {
            Prop::Or(Box::new(subst_prop(a, var, value)), Box::new(subst_prop(b, var, value)))
        }
        Prop::Implies(a, b) => {
            Prop::Implies(Box::new(subst_prop(a, var, value)), Box::new(subst_prop(b, var, value)))
        }
        Prop::Forall(s, _) | Prop::Exists(s, _) if *s == var => p.clone(),
        Prop::Forall(s, a) => Prop::Forall(*s, Box::new(subst_prop(a, var, value))),
        Prop::Exists(s, a) => Prop::Exists(*s, Box::new(subst_prop(a, var, value))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn checks_arithmetic_and_substitutes() {
        let mut syms = Symbols::new();
        let x = syms.intern("x");
        let ctx: Ctx = [(x, Ty::Int)].into_iter().collect();
        let t = Term::bin(BinOp::Lt, Term::Var(x), Term::Int(5));
        assert_eq!(type_of(&t, &ctx), Ok(Ty::Bool));
        let s = subst_term(&t, x, &Term::Int(3));
        assert_eq!(type_of(&s, &HashMap::new()), Ok(Ty::Bool));
    }
}
