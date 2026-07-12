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

/// A fixed-width integer type: its signedness and bit width.
///
/// Supported widths are `8, 16, 32, 64, 128` (both signednesses). Bounds are
/// exposed as `i128`, which represents every bound exactly **except** the maximum
/// of a 128-bit *unsigned* type (`u128::MAX == 2^128 - 1`), which does not fit in
/// `i128`. For that one case [`IntTy::max`] saturates to `i128::MAX` and the exact
/// value is available via [`IntTy::max_u128`].
///
/// ## Why the bounds are not always embeddable in a [`Term`]
///
/// `Term::Int` carries an `i128` (the kernel's constant representation, matched
/// exhaustively across the trusted solver). This embeds every bound exactly
/// **except** the true maximum of a 128-bit *unsigned* type (`u128::MAX ==
/// 2^128 - 1`), which does not fit in `i128`. The verifier accounts for this one
/// remaining case by clamping/dropping that bound *in the sound direction* (see
/// [`IntTy::overflow_lo_i64`]/[`IntTy::overflow_hi_i64`] for overflow
/// *obligations* and [`IntTy::assume_lo_i64`]/[`IntTy::assume_hi_i64`] for range
/// *assumptions*), never by truncating it (which would silently emit a wrong
/// bound).
///
/// ## The `u128` boundary, in practice
///
/// A `u128` *literal* whose magnitude exceeds `i128::MAX` still lexes (see
/// `rv_syntax::Tok::Int`'s doc comment: it is parsed as `u128` then
/// bit-reinterpreted into `Term::Int`'s `i128` carrier, landing as a negative
/// `i128`). But every `u128` value automatically carries a `>= 0` range
/// obligation/assumption (see `rv_infer::range_assumption`), and that check
/// uses ordinary signed `i128` comparison — so a magnitude above `i128::MAX`
/// reads back as negative and **fails** that check. This is a sound rejection
/// (not silent truncation or a crash), but it means the practically supported
/// `u128` range for verified code is `0..=i128::MAX`, not the full
/// `0..=u128::MAX`. Widening the solver itself past `i128`-exact rational
/// arithmetic (e.g. to a bignum `Rat`) would be needed to lift this; see
/// `rv-driver`'s `i128_tests` module for the exact passing/failing cases.
///
/// Separately, *checked* (non-`wrapping_*`) arithmetic on a 128-bit-wide
/// destination is sound-but-incomplete near the true boundary: proving the
/// result stays within `[i128::MIN, i128::MAX]` requires the trusted LIA
/// solver to normalize a comparison against those exact values, which can
/// itself overflow the solver's own `i128`-exact rational arithmetic (e.g.
/// negating `i128::MIN`). `wrapping_*` intrinsics sidestep this (they opt out
/// of the overflow obligation entirely) and are the currently-recommended way
/// to do 128-bit arithmetic that must verify.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct IntTy {
    pub signed: bool,
    pub bits: u8,
}
impl IntTy {
    /// The smallest representable value, as `i128`.
    ///
    /// Exact for every supported width: an unsigned type's minimum is `0`, and a
    /// signed `N`-bit type's minimum `-2^(N-1)` fits in `i128` for `N <= 128`
    /// (`i128::MIN` for `N == 128`). Panic-free for all widths `<= 128`.
    pub fn min(&self) -> i128 {
        if !self.signed {
            return 0;
        }
        if self.bits >= 128 {
            // `-2^127` is exactly `i128::MIN`; computing it via a shift + negate
            // would overflow, so return the constant directly.
            return i128::MIN;
        }
        -(1i128 << (self.bits - 1))
    }
    /// The largest representable value, as `i128`.
    ///
    /// Exact for every supported width **except** 128-bit unsigned, whose true
    /// maximum `2^128 - 1` exceeds `i128::MAX`; that case saturates to `i128::MAX`
    /// (use [`IntTy::max_u128`] for the exact value). Panic-free for all widths
    /// `<= 128`.
    pub fn max(&self) -> i128 {
        if self.signed {
            if self.bits >= 128 {
                return i128::MAX; // exactly `2^127 - 1`
            }
            (1i128 << (self.bits - 1)) - 1
        } else {
            if self.bits >= 127 {
                // `2^127 - 1 == i128::MAX`; `2^128 - 1` saturates to it too. The
                // naive `(1 << bits) - 1` would overflow `i128` for these widths.
                return i128::MAX;
            }
            (1i128 << self.bits) - 1
        }
    }
    /// The exact largest representable value as an unsigned 128-bit magnitude.
    ///
    /// Unlike [`IntTy::max`] this loses no precision for `u128` (`u128::MAX`). For
    /// signed types it returns the (non-negative) signed maximum widened to `u128`.
    pub fn max_u128(&self) -> u128 {
        if self.signed {
            if self.bits >= 128 {
                return i128::MAX as u128;
            }
            (1u128 << (self.bits - 1)) - 1
        } else if self.bits >= 128 {
            u128::MAX
        } else {
            (1u128 << self.bits) - 1
        }
    }

    /// The lower bound of the **overflow-obligation** range, as an `i128` safe to
    /// embed in a `Term` (the kernel's `Term::Int` carrier is `i128`). This is
    /// simply [`IntTy::min`]: since every supported width's true minimum fits
    /// exactly in `i128`, no clamping is needed (unlike the old `i64` carrier).
    pub fn overflow_lo_i64(&self) -> i128 {
        self.min()
    }
    /// The upper bound of the **overflow-obligation** range, as an `i128` safe to
    /// embed in a `Term`. Clamped *inward* to `i128::MAX` for `u128` (whose true
    /// maximum `2^128 - 1` does not fit in `i128`) so the obligation range stays a
    /// subset of the true range (sound but incomplete for `u128` values in
    /// `(i128::MAX, u128::MAX]`; see [`IntTy::max_u128`]).
    pub fn overflow_hi_i64(&self) -> i128 {
        self.max()
    }
    /// The type's true minimum as an `i128`. Always exact: every supported
    /// width's minimum fits in `i128`, so a range **assumption** can always use
    /// this bound exactly (no dropping needed, unlike the old `i64` carrier).
    pub fn assume_lo_i64(&self) -> Option<i128> {
        Some(self.min())
    }
    /// The type's true maximum as an `i128`, or `None` when it does not fit
    /// exactly (only `u128`, whose true maximum `u128::MAX` exceeds `i128::MAX`).
    /// Used for a range **assumption** (a hypothesis we add): an assumption must
    /// be weaker-or-equal to the truth, so a bound that cannot be represented
    /// exactly is *dropped* (returns `None`) rather than clamped — clamping an
    /// assumption inward would assert a *false* fact and be unsound.
    pub fn assume_hi_i64(&self) -> Option<i128> {
        if self.signed || self.bits < 128 {
            Some(self.max())
        } else {
            // u128: true max is `2^128 - 1`, which exceeds `i128::MAX`.
            None
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
    /// 64-bit float (`f64`). Opaque to the linear-arithmetic solver.
    Float,
    /// An immutable string (`String`). Opaque to the solver.
    Str,
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
    /// An integer literal. Carries a full `i128` magnitude, sufficient to embed
    /// every `i128` value exactly and every `u128` value up to `i128::MAX`
    /// (`u128` values above `i128::MAX` cannot be embedded as a literal `Term`;
    /// see [`IntTy::max_u128`] / [`IntTy::assume_hi_i64`]).
    Int(i128),
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

    #[test]
    fn small_int_bounds_are_exact() {
        let u8t = IntTy { signed: false, bits: 8 };
        assert_eq!((u8t.min(), u8t.max()), (0, 255));
        let i8t = IntTy { signed: true, bits: 8 };
        assert_eq!((i8t.min(), i8t.max()), (-128, 127));
        let i32t = IntTy { signed: true, bits: 32 };
        assert_eq!((i32t.min(), i32t.max()), (i32::MIN as i128, i32::MAX as i128));
        // Exact bounds fit `i128`, so both the obligation and assumption helpers
        // reproduce them precisely.
        assert_eq!(i32t.overflow_lo_i64(), i32::MIN as i128);
        assert_eq!(i32t.overflow_hi_i64(), i32::MAX as i128);
        assert_eq!(i32t.assume_lo_i64(), Some(i32::MIN as i128));
        assert_eq!(i32t.assume_hi_i64(), Some(i32::MAX as i128));
    }

    #[test]
    fn signed_128_bounds_are_panic_free_and_exact() {
        let i128t = IntTy { signed: true, bits: 128 };
        assert_eq!(i128t.min(), i128::MIN);
        assert_eq!(i128t.max(), i128::MAX);
        // Both bounds fit `i128` exactly now (the `Term::Int` carrier), so
        // obligations *and* assumptions reproduce them precisely.
        assert_eq!(i128t.assume_lo_i64(), Some(i128::MIN));
        assert_eq!(i128t.assume_hi_i64(), Some(i128::MAX));
        assert_eq!(i128t.overflow_lo_i64(), i128::MIN);
        assert_eq!(i128t.overflow_hi_i64(), i128::MAX);
    }

    #[test]
    fn unsigned_128_bounds_are_correct() {
        let u128t = IntTy { signed: false, bits: 128 };
        assert_eq!(u128t.min(), 0);
        // `max()` saturates (u128::MAX does not fit i128) ...
        assert_eq!(u128t.max(), i128::MAX);
        // ... but the exact magnitude is available and correct.
        assert_eq!(u128t.max_u128(), u128::MAX);
        assert_eq!(u128t.overflow_lo_i64(), 0);
        // Obligation upper bound clamps to `i128::MAX` (the one remaining case
        // that cannot be embedded exactly: `u128::MAX == 2^128 - 1`).
        assert_eq!(u128t.overflow_hi_i64(), i128::MAX);
        assert_eq!(u128t.assume_lo_i64(), Some(0));
        assert_eq!(u128t.assume_hi_i64(), None);
    }

    #[test]
    fn u64_upper_bound_is_now_exact_under_the_i128_carrier() {
        // Regression (historical): under the old `i64` `Term::Int` carrier,
        // `u64::MAX as i64 == -1`, so a range *assumption* had to drop the upper
        // bound entirely to avoid asserting the false fact `x <= -1`. Now that
        // `Term::Int` carries `i128`, `u64::MAX` fits exactly and both the
        // obligation and the assumption can use it precisely.
        let u64t = IntTy { signed: false, bits: 64 };
        assert_eq!(u64t.max(), u64::MAX as i128);
        assert_eq!(u64t.assume_hi_i64(), Some(u64::MAX as i128));
        assert_eq!(u64t.assume_lo_i64(), Some(0));
        assert_eq!(u64t.overflow_hi_i64(), u64::MAX as i128);
        assert_eq!(u64t.overflow_lo_i64(), 0);
    }
}
