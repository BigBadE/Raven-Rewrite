//! The **independently checkable** core of the linear-arithmetic + congruence
//! decision procedure: everything a party who does *not* trust `rv-solve` needs to
//! re-verify one of its positive results, and nothing more.
//!
//! # Why this lives in `rv-logic`
//!
//! `rv-solve` proves an obligation `ctx ⟹ goal` by refuting `ctx ∧ ¬goal`: it
//! enumerates that formula's DNF and shows **every** disjunct is unsatisfiable. The
//! refutation *search* (Fourier–Motzkin elimination, DNF construction, congruence
//! saturation) is intricate and stays in `rv-solve`. But the *checker* — the small,
//! obviously-sound function that re-verifies an emitted certificate by pure arithmetic
//! and substitution — belongs here, in the trust base, so that a consumer holding only
//! an [`Outcome`](crate::Outcome) can re-run it **without depending on the solver**.
//!
//! Concretely: the types below ([`Atom`], [`Literal`], [`LinConstraint`], [`Rat`],
//! [`LiaCertificate`], …) are exactly the closed set the checker touches. `rv-solve`
//! re-exports them and keeps *producing* them from its search; but the search is now
//! untrusted — if it emits a wrong certificate, [`LiaCertificate::check`] rejects it.
//!
//! # What a certificate contains
//!
//! A [`LiaCertificate`] proves a *whole* formula (a list of DNF disjuncts) is
//! unsatisfiable: one [`DisjunctCert`] per disjunct, since UNSAT of the disjunction
//! requires UNSAT of every disjunct. Each [`DisjunctCert`] is one of three sound
//! refutations of a single conjunction of literals:
//!
//! * [`DisjunctCert::OpaqueClash`] — an opaque atom asserted both positively and
//!   negatively (`p ∧ ¬p`).
//! * [`DisjunctCert::EqualityClash`] — a congruence-closure contradiction: asserted
//!   equalities force `l = r`, yet `l ≠ r` is asserted.
//! * [`DisjunctCert::LinearRefutation`] — a **Farkas** refutation of the linear part,
//!   one [`FarkasCert`] per disequality-side branch.
//!
//! # The Farkas core
//!
//! After normalization every asserted comparison becomes some `≤ 0` constraints. A
//! [`FarkasCert`] is a vector of **non-negative** rational multipliers `λ`, one per
//! constraint. Checking is arithmetic with no search: form `Σ λᵢ · exprᵢ`; if the
//! result is a variable-free **strictly positive** constant then we have derived
//! `c ≤ 0` with `c > 0` — a manifest contradiction.
//!
//! # Independence of the checker
//!
//! [`LiaCertificate::check`] takes only the *original DNF disjuncts* (the literals the
//! solver started from) and re-derives the normalized constraints itself via the pure
//! [`cmp_to_constraints`] / [`cmp_to_disequality`] here — total, syntax-directed
//! functions, not the search. It then does arithmetic and a union–find rebuild. It calls
//! **nothing** in the Fourier–Motzkin engine. So a bug in the search cannot make the
//! checker accept an unsound certificate: at worst the search emits a certificate the
//! checker rejects.

use rv_core::{BinOp, Sym, Term, UnOp};
use std::collections::BTreeMap;

/// The DNF-size cap shared by the solver's search and the checker's independent
/// re-derivation. Both must use the *same* value so [`disjuncts_of`] reproduces exactly
/// the disjunct list the solver refuted. DNF size is worst-case exponential; this
/// generous-but-finite bound avoids pathological blow-up while staying sound (refusing
/// to decide is never unsound).
pub const MAX_DISJUNCTS: usize = 4096;

// ===========================================================================
// Exact rationals
// ===========================================================================

/// An exact rational `num/den`, kept reduced with `den > 0`.
///
/// Rationals are exact (`i128` numerator / `i128` denominator). Any arithmetic overflow
/// is caught and reported as `None` rather than wrapping — wrapping could be unsound.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Rat {
    num: i128,
    den: i128,
}

impl Rat {
    /// Construct a rational from an integer.
    pub fn from_int(n: i128) -> Rat {
        Rat { num: n, den: 1 }
    }
    /// A non-negative rational is a valid Farkas multiplier.
    pub fn is_non_negative(&self) -> bool {
        self.num >= 0
    }
    /// Exact rational addition (checked).
    pub fn checked_add(self, other: Rat) -> Option<Rat> {
        // a/b + c/d = (a*d + c*b) / (b*d)
        let n = self.num.checked_mul(other.den)?.checked_add(other.num.checked_mul(self.den)?)?;
        let d = self.den.checked_mul(other.den)?;
        Rat::new(n, d)
    }
    /// Exact rational multiplication (checked).
    pub fn checked_mul(self, other: Rat) -> Option<Rat> {
        let n = self.num.checked_mul(other.num)?;
        let d = self.den.checked_mul(other.den)?;
        Rat::new(n, d)
    }
    /// Is this value strictly positive?
    pub fn positive(&self) -> bool {
        self.num > 0
    }
    /// Is this value strictly negative? Exposed for the search's pivot selection.
    pub fn negative(&self) -> bool {
        self.num < 0
    }
    /// The additive identity. Exposed so the search can seed Farkas multiplier vectors.
    pub fn zero_rat() -> Rat {
        Rat::zero()
    }
    /// Exact negation (checked). Exposed for the search's Farkas elimination.
    pub fn checked_neg(self) -> Option<Rat> {
        self.neg()
    }
    fn new(num: i128, den: i128) -> Option<Rat> {
        if den == 0 {
            return None;
        }
        let (mut n, mut d) = (num, den);
        if d < 0 {
            // Keep the denominator positive (so sign lives in the numerator).
            n = n.checked_neg()?;
            d = d.checked_neg()?;
        }
        let g = gcd(n.unsigned_abs(), d.unsigned_abs()) as i128;
        if g != 0 {
            n /= g;
            d /= g;
        }
        Some(Rat { num: n, den: d })
    }
    fn zero() -> Rat {
        Rat { num: 0, den: 1 }
    }
    fn is_zero(&self) -> bool {
        self.num == 0
    }
    fn is_positive(&self) -> bool {
        self.num > 0
    }
    fn neg(self) -> Option<Rat> {
        Some(Rat { num: self.num.checked_neg()?, den: self.den })
    }
}

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

// ===========================================================================
// Linear expressions
// ===========================================================================

/// A linear expression `Σ cᵢ·xᵢ + k`, with coefficients/constant as exact rationals.
/// A `BTreeMap` (ordered, deduped) keeps the representation canonical.
#[derive(Clone, Debug)]
pub struct LinExpr {
    coeffs: BTreeMap<Sym, Rat>,
    constant: Rat,
}

impl LinExpr {
    fn constant(k: Rat) -> LinExpr {
        LinExpr { coeffs: BTreeMap::new(), constant: k }
    }
    fn var(s: Sym) -> LinExpr {
        let mut m = BTreeMap::new();
        m.insert(s, Rat::from_int(1));
        LinExpr { coeffs: m, constant: Rat::zero() }
    }

    fn add(&self, other: &LinExpr) -> Option<LinExpr> {
        let mut out = self.clone();
        out.constant = out.constant.checked_add(other.constant)?;
        for (s, c) in &other.coeffs {
            let entry = out.coeffs.entry(*s).or_insert_with(Rat::zero);
            *entry = entry.checked_add(*c)?;
        }
        out.prune();
        Some(out)
    }
    fn neg(&self) -> Option<LinExpr> {
        let mut out = LinExpr { coeffs: BTreeMap::new(), constant: self.constant.neg()? };
        for (s, c) in &self.coeffs {
            out.coeffs.insert(*s, c.neg()?);
        }
        Some(out)
    }
    fn sub(&self, other: &LinExpr) -> Option<LinExpr> {
        self.add(&other.neg()?)
    }
    fn scale(&self, k: Rat) -> Option<LinExpr> {
        let mut out = LinExpr { coeffs: BTreeMap::new(), constant: self.constant.checked_mul(k)? };
        for (s, c) in &self.coeffs {
            out.coeffs.insert(*s, c.checked_mul(k)?);
        }
        out.prune();
        Some(out)
    }
    /// Drop zero coefficients so canonical forms compare cleanly.
    fn prune(&mut self) {
        self.coeffs.retain(|_, c| !c.is_zero());
    }
    /// If this expression has no variables, return its constant value.
    fn as_constant(&self) -> Option<Rat> {
        if self.coeffs.is_empty() {
            Some(self.constant)
        } else {
            None
        }
    }

    /// Public checked scale — multiply a constraint's `≤ 0` expression by a non-negative
    /// Farkas coefficient.
    pub fn checked_scale(&self, k: Rat) -> Option<LinExpr> {
        self.scale(k)
    }
    /// Public checked add — sum scaled constraints into one row.
    pub fn checked_add(&self, other: &LinExpr) -> Option<LinExpr> {
        self.add(other)
    }
    /// The all-zero expression (the additive identity), the seed for a Farkas sum.
    pub fn zero_expr() -> LinExpr {
        LinExpr::constant(Rat::zero())
    }
    /// The coefficient of variable `s` (zero if absent). Exposed so the search engine
    /// in `rv-solve` can pivot on a variable during Fourier–Motzkin elimination.
    pub fn coeff(&self, s: Sym) -> Rat {
        self.coeffs.get(&s).copied().unwrap_or_else(Rat::zero)
    }
    /// If this expression is variable-free, its constant value; else `None`. Exposed for
    /// the search's contradiction scan.
    pub fn constant_value(&self) -> Option<Rat> {
        self.as_constant()
    }
    /// The variables (with non-zero coefficients) in this expression, in `Sym` order.
    pub fn var_syms(&self) -> impl Iterator<Item = Sym> + '_ {
        self.coeffs.keys().copied()
    }
    /// Is this expression a *variable-free* constant that is **strictly positive**?
    /// A `≤ 0` constraint whose expression is such a constant is the manifestly false
    /// inequality (`c ≤ 0` with `c > 0`) — the target of every Farkas certificate.
    pub fn is_positive_constant(&self) -> bool {
        matches!(self.as_constant(), Some(c) if c.is_positive())
    }
}

/// Lower a `Term` to a linear expression, or `None` if it is not linear (e.g.
/// `Var*Var`, `Div`, `Mod`, or any overflow). `None` ⇒ the enclosing comparison is
/// treated as opaque, which is sound.
fn linearize(t: &Term) -> Option<LinExpr> {
    match t {
        Term::Int(n) => Some(LinExpr::constant(Rat::from_int(*n as i128))),
        Term::Var(s) => Some(LinExpr::var(*s)),
        Term::Bool(_) => None,
        Term::Un(UnOp::Neg, a) => linearize(a)?.neg(),
        Term::Un(UnOp::Not, _) => None,
        Term::Field(..) => None,
        Term::App(..) => None,
        Term::Bin(op, a, b) => match op {
            BinOp::Add => linearize(a)?.add(&linearize(b)?),
            BinOp::Sub => linearize(a)?.sub(&linearize(b)?),
            BinOp::Mul => {
                let (la, lb) = (linearize(a)?, linearize(b)?);
                if let Some(k) = lb.as_constant() {
                    la.scale(k)
                } else if let Some(k) = la.as_constant() {
                    lb.scale(k)
                } else {
                    None // Var * Var — non-linear.
                }
            }
            _ => None,
        },
    }
}

// ===========================================================================
// Constraints and disequalities
// ===========================================================================

/// A single linear constraint in canonical form `expr ≤ 0`.
#[derive(Clone, Debug)]
pub struct LinConstraint {
    expr: LinExpr,
}

impl LinConstraint {
    /// `expr ≤ 0`.
    pub fn le_zero(expr: LinExpr) -> LinConstraint {
        LinConstraint { expr }
    }
    /// The `≤ 0` left-hand expression. The checker reads this to form the Farkas
    /// combination `Σ λᵢ · exprᵢ`.
    pub fn expr(&self) -> &LinExpr {
        &self.expr
    }
}

/// A disequality `lhs ≠ rhs` over linear expressions, stored as `diff = lhs - rhs`.
/// It is equivalent to the disjunction `diff < 0 ∨ diff > 0`, i.e. (over integers)
/// `diff ≤ -1  ∨  diff ≥ 1`.
#[derive(Clone, Debug)]
pub struct Disequality {
    diff: LinExpr, // lhs - rhs
}

impl Disequality {
    /// The two `≤ 0` constraints, one per side of the disjunction:
    /// * `lhs < rhs`  ⇒  `diff + 1 ≤ 0`;
    /// * `lhs > rhs`  ⇒  `-diff + 1 ≤ 0`.
    ///
    /// Both directions use integrality (the `±1` tightening), which is sound.
    pub fn sides(&self) -> Vec<LinConstraint> {
        let mut out = Vec::new();
        if let Some(lt) = self.diff.add(&LinExpr::constant(Rat::from_int(1))) {
            out.push(LinConstraint::le_zero(lt));
        }
        if let Some(neg) = self.diff.neg() {
            if let Some(gt) = neg.add(&LinExpr::constant(Rat::from_int(1))) {
                out.push(LinConstraint::le_zero(gt));
            }
        }
        out
    }

    /// The underlying difference expression `lhs - rhs`. Exposed so the search engine
    /// (in `rv-solve`) can reuse it for its diagnostic counterexample hunt.
    pub fn diff(&self) -> &LinExpr {
        &self.diff
    }
}

/// If `lhs op rhs` (after absorbing `negated`) is a **disequality** `≠` over linear
/// expressions, return it; otherwise `None`.
pub fn cmp_to_disequality(
    op: BinOp,
    lhs: &Term,
    rhs: &Term,
    negated: bool,
) -> Option<Disequality> {
    let eff = if negated { negate_cmp(op)? } else { op };
    if eff != BinOp::Ne {
        return None;
    }
    let l = linearize(lhs)?;
    let r = linearize(rhs)?;
    Some(Disequality { diff: l.sub(&r)? })
}

/// Translate a (possibly negated) integer comparison `lhs op rhs` into an equivalent
/// **set** of `≤ 0` constraints, or `None` if either side isn't linear **or** the
/// comparison is a disequality.
///
/// Integer strictness: `a < b ⟺ a ≤ b − 1` and `a > b ⟺ a ≥ b + 1` — the one place we
/// use integrality, and it only ever tightens a constraint, so it is sound.
pub fn cmp_to_constraints(
    op: BinOp,
    lhs: &Term,
    rhs: &Term,
    negated: bool,
) -> Option<Vec<LinConstraint>> {
    let eff = if negated { negate_cmp(op)? } else { op };

    let l = linearize(lhs)?;
    let r = linearize(rhs)?;

    match eff {
        BinOp::Le => Some(vec![LinConstraint::le_zero(l.sub(&r)?)]),
        BinOp::Ge => Some(vec![LinConstraint::le_zero(r.sub(&l)?)]),
        BinOp::Lt => {
            let e = l.sub(&r)?.add(&LinExpr::constant(Rat::from_int(1)))?;
            Some(vec![LinConstraint::le_zero(e)])
        }
        BinOp::Gt => {
            let e = r.sub(&l)?.add(&LinExpr::constant(Rat::from_int(1)))?;
            Some(vec![LinConstraint::le_zero(e)])
        }
        BinOp::Eq => {
            Some(vec![LinConstraint::le_zero(l.sub(&r)?), LinConstraint::le_zero(r.sub(&l)?)])
        }
        BinOp::Ne => None,
        _ => None,
    }
}

/// Evaluate a `LinExpr` at an integer assignment, returning the exact rational value
/// (variables not in `assign` are treated as 0). Exposed for the search's diagnostic
/// counterexample evaluation.
pub fn eval_lin(e: &LinExpr, assign: &BTreeMap<Sym, i64>) -> Option<Rat> {
    let mut acc = e.constant;
    for (s, c) in &e.coeffs {
        let val = Rat::from_int(*assign.get(s).unwrap_or(&0) as i128);
        acc = acc.checked_add(c.checked_mul(val)?)?;
    }
    Some(acc)
}

/// Is a rational value strictly positive? (helper for the search's model check.)
pub fn rat_is_positive(r: Rat) -> bool {
    r.is_positive()
}
/// Is a rational value zero? (helper for the search's model check.)
pub fn rat_is_zero(r: Rat) -> bool {
    r.is_zero()
}

/// The effective comparison operator after absorbing a literal's `negated` flag.
/// `None` if `op` is not a comparison.
pub fn effective_cmp(op: BinOp, negated: bool) -> Option<BinOp> {
    if negated {
        negate_cmp(op)
    } else {
        match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => Some(op),
            _ => None,
        }
    }
}

/// Negate a comparison operator (used to absorb a literal's `negated` flag).
fn negate_cmp(op: BinOp) -> Option<BinOp> {
    Some(match op {
        BinOp::Eq => BinOp::Ne,
        BinOp::Ne => BinOp::Eq,
        BinOp::Lt => BinOp::Ge,
        BinOp::Le => BinOp::Gt,
        BinOp::Gt => BinOp::Le,
        BinOp::Ge => BinOp::Lt,
        _ => return None,
    })
}

// ===========================================================================
// Atoms and literals (the DNF alphabet)
// ===========================================================================

/// An atomic, indivisible proposition.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Atom {
    /// An integer comparison `lhs ⋈ rhs`.
    Cmp { op: BinOp, lhs: Term, rhs: Term },
    /// Anything we do not interpret. Compared only by syntactic identity.
    Opaque(OpaqueAtom),
}

/// Wrapper distinguishing the two kinds of opaque source so they never alias.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum OpaqueAtom {
    /// An opaque boolean-valued term.
    Term(Term),
    /// An opaque proposition (e.g. a quantifier) that we cannot decompose.
    Prop(Box<rv_core::Prop>),
}

/// A literal: an atom with a polarity.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Literal {
    pub atom: Atom,
    /// `true` means the atom is negated (`¬atom`).
    pub negated: bool,
}

// ===========================================================================
// Equality / congruence closure (the checker's union–find)
// ===========================================================================

/// A union–find over opaque terms, keyed by syntactic identity, with congruence
/// closure over uninterpreted applications. Used both by the search and — crucially —
/// by the checker to *rebuild* an equality clash from its recorded asserted equalities.
#[derive(Default)]
pub struct EqClosure {
    terms: Vec<Term>,
    parent: Vec<usize>,
    size: Vec<usize>,
}

impl EqClosure {
    pub fn new() -> Self {
        Self::default()
    }

    fn lookup(&self, t: &Term) -> Option<usize> {
        self.terms.iter().position(|x| x == t)
    }

    fn id(&mut self, t: &Term) -> usize {
        if let Some(i) = self.lookup(t) {
            return i;
        }
        let i = self.parent.len();
        self.parent.push(i);
        self.size.push(1);
        self.terms.push(t.clone());
        if let Term::App(_, args) = t {
            for a in args.clone() {
                self.id(&a);
            }
        }
        i
    }

    fn find(&mut self, mut i: usize) -> usize {
        while self.parent[i] != i {
            self.parent[i] = self.parent[self.parent[i]];
            i = self.parent[i];
        }
        i
    }

    /// Assert `a == b`: union their classes.
    pub fn assert_eq(&mut self, a: &Term, b: &Term) {
        let (ia, ib) = (self.id(a), self.id(b));
        self.union(ia, ib);
    }

    /// Intern `t` (and, for an `App`, its arguments) without asserting anything.
    pub fn see(&mut self, t: &Term) {
        self.id(t);
    }

    fn union(&mut self, ia: usize, ib: usize) {
        let (ra, rb) = (self.find(ia), self.find(ib));
        if ra == rb {
            return;
        }
        let (small, large) = if self.size[ra] < self.size[rb] { (ra, rb) } else { (rb, ra) };
        self.parent[small] = large;
        self.size[large] += self.size[small];
    }

    /// Saturate the **congruence closure** over uninterpreted applications to a fixpoint.
    pub fn close(&mut self) {
        loop {
            let apps: Vec<usize> = (0..self.terms.len())
                .filter(|&i| matches!(self.terms[i], Term::App(..)))
                .collect();
            let mut changed = false;
            for x in 0..apps.len() {
                for y in (x + 1)..apps.len() {
                    let (i, j) = (apps[x], apps[y]);
                    if self.find(i) != self.find(j) && self.congruent(i, j) {
                        self.union(i, j);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn congruent(&mut self, i: usize, j: usize) -> bool {
        let (ti, tj) = (self.terms[i].clone(), self.terms[j].clone());
        let (Term::App(f, a), Term::App(g, b)) = (&ti, &tj) else {
            return false;
        };
        if f != g || a.len() != b.len() {
            return false;
        }
        a.iter().zip(b.iter()).all(|(x, y)| {
            let (ix, iy) = (self.id(x), self.id(y));
            self.find(ix) == self.find(iy)
        })
    }

    /// Are `a` and `b` currently forced equal by the asserted equalities? `false` if
    /// either term was never seen.
    pub fn equal(&mut self, a: &Term, b: &Term) -> bool {
        let (ia, ib) = match (self.lookup(a), self.lookup(b)) {
            (Some(ia), Some(ib)) => (ia, ib),
            _ => return false,
        };
        self.find(ia) == self.find(ib)
    }
}

// ===========================================================================
// Propositional normalization (NNF + DNF) — needed to bind a certificate to an
// obligation independently of the solver.
// ===========================================================================

/// An NNF formula: negations pushed to the literals.
enum Nnf {
    Const(bool),
    Lit(Literal),
    And(Box<Nnf>, Box<Nnf>),
    Or(Box<Nnf>, Box<Nnf>),
}

fn lit_pos(atom: Atom) -> Literal {
    Literal { atom, negated: false }
}
fn lit_neg(atom: Atom) -> Literal {
    Literal { atom, negated: true }
}

/// Convert a `Prop` to NNF. `negate` requests `¬prop`. This is the *same* total,
/// syntax-directed translation the solver uses; keeping a copy here lets the checker
/// re-derive the DNF of `ctx ∧ ¬goal` itself, so it never has to trust the disjuncts a
/// certificate ships with — it confirms they are exactly the ones this obligation yields.
fn to_nnf(p: &rv_core::Prop, negate: bool) -> Nnf {
    use rv_core::Prop;
    match p {
        Prop::True => Nnf::Const(!negate),
        Prop::False => Nnf::Const(negate),
        Prop::And(a, b) => {
            let (la, lb) = (to_nnf(a, negate), to_nnf(b, negate));
            if negate {
                Nnf::Or(Box::new(la), Box::new(lb))
            } else {
                Nnf::And(Box::new(la), Box::new(lb))
            }
        }
        Prop::Or(a, b) => {
            let (la, lb) = (to_nnf(a, negate), to_nnf(b, negate));
            if negate {
                Nnf::And(Box::new(la), Box::new(lb))
            } else {
                Nnf::Or(Box::new(la), Box::new(lb))
            }
        }
        Prop::Not(a) => to_nnf(a, !negate),
        Prop::Implies(a, b) => {
            if negate {
                Nnf::And(Box::new(to_nnf(a, false)), Box::new(to_nnf(b, true)))
            } else {
                Nnf::Or(Box::new(to_nnf(a, true)), Box::new(to_nnf(b, false)))
            }
        }
        Prop::Holds(t) => term_to_nnf(t, negate),
        Prop::Forall(_, _) | Prop::Exists(_, _) => {
            let atom = Atom::Opaque(OpaqueAtom::Prop(Box::new(p.clone())));
            Nnf::Lit(if negate { lit_neg(atom) } else { lit_pos(atom) })
        }
    }
}

fn term_to_nnf(t: &Term, negate: bool) -> Nnf {
    match t {
        Term::Bool(b) => Nnf::Const(*b ^ negate),
        Term::Un(UnOp::Not, inner) => term_to_nnf(inner, !negate),
        Term::Bin(BinOp::And, a, b) => {
            let (la, lb) = (term_to_nnf(a, negate), term_to_nnf(b, negate));
            if negate {
                Nnf::Or(Box::new(la), Box::new(lb))
            } else {
                Nnf::And(Box::new(la), Box::new(lb))
            }
        }
        Term::Bin(BinOp::Or, a, b) => {
            let (la, lb) = (term_to_nnf(a, negate), term_to_nnf(b, negate));
            if negate {
                Nnf::And(Box::new(la), Box::new(lb))
            } else {
                Nnf::Or(Box::new(la), Box::new(lb))
            }
        }
        Term::Bin(op, a, b) if is_cmp(*op) => {
            let atom = Atom::Cmp { op: *op, lhs: (**a).clone(), rhs: (**b).clone() };
            Nnf::Lit(if negate { lit_neg(atom) } else { lit_pos(atom) })
        }
        _ => {
            let atom = Atom::Opaque(OpaqueAtom::Term(t.clone()));
            Nnf::Lit(if negate { lit_neg(atom) } else { lit_pos(atom) })
        }
    }
}

fn is_cmp(op: BinOp) -> bool {
    matches!(op, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
}

/// Enumerate the DNF of an NNF formula, or `None` if it exceeds `max` disjuncts.
fn dnf(f: &Nnf, max: usize) -> Option<Vec<Vec<Literal>>> {
    match f {
        Nnf::Const(true) => Some(vec![vec![]]),
        Nnf::Const(false) => Some(vec![]),
        Nnf::Lit(l) => Some(vec![vec![l.clone()]]),
        Nnf::Or(a, b) => {
            let mut da = dnf(a, max)?;
            let db = dnf(b, max)?;
            da.extend(db);
            if da.len() > max {
                return None;
            }
            Some(da)
        }
        Nnf::And(a, b) => {
            let da = dnf(a, max)?;
            let db = dnf(b, max)?;
            if da.len().checked_mul(db.len()).is_none_or(|n| n > max) {
                return None;
            }
            let mut out = Vec::with_capacity(da.len() * db.len());
            for ca in &da {
                for cb in &db {
                    let mut merged = ca.clone();
                    merged.extend(cb.clone());
                    out.push(merged);
                }
            }
            Some(out)
        }
    }
}

/// Re-derive the DNF disjuncts of `ctx ∧ ¬goal` for an obligation, independently of the
/// solver. The `max` cap must match the solver's so the enumeration is identical.
/// Returns `None` on overflow (then a certificate cannot be bound and is rejected).
pub fn disjuncts_of(ctx: &rv_core::Prop, goal: &rv_core::Prop, max: usize) -> Option<Vec<Vec<Literal>>> {
    let formula = rv_core::Prop::And(
        Box::new(ctx.clone()),
        Box::new(rv_core::Prop::Not(Box::new(goal.clone()))),
    );
    let nnf = to_nnf(&formula, false);
    dnf(&nnf, max)
}

// ===========================================================================
// The certificate and its checker
// ===========================================================================

/// A checkable proof that a formula (a list of DNF disjuncts of `ctx ∧ ¬goal`) is
/// unsatisfiable — i.e. that the obligation is valid. One [`DisjunctCert`] per disjunct.
#[derive(Clone, Debug)]
pub struct LiaCertificate {
    /// One refutation per disjunct. The checker also verifies the *count* matches the
    /// disjuncts it is handed, so a certificate cannot silently skip a disjunct.
    pub disjuncts: Vec<DisjunctCert>,
}

/// A refutation of a single disjunct (a conjunction of literals).
#[derive(Clone, Debug)]
pub enum DisjunctCert {
    /// `p ∧ ¬p` for an opaque atom `p`.
    OpaqueClash { atom: Atom },

    /// A congruence-closure contradiction. `asserted_eqs` are the `(l, r)` pairs the
    /// solver unioned; `diseq` is an asserted `(l, r)` whose sides those equalities force
    /// equal. The checker rebuilds the closure from `asserted_eqs` alone, confirms the
    /// clash, and confirms both the equalities and the disequality are genuinely asserted.
    EqualityClash {
        asserted_eqs: Vec<(Term, Term)>,
        diseq: (Term, Term),
    },

    /// A Farkas refutation of the linear part. `branches` covers every combination of
    /// disequality sides; each branch must be linearly UNSAT.
    LinearRefutation { branches: Vec<FarkasCert> },
}

/// A Farkas certificate for one linear branch: `multipliers[i]` is the non-negative
/// rational coefficient applied to the `i`-th `≤ 0` constraint of that branch. The claim
/// is that `Σ multipliers[i]·exprᵢ` is a positive constant.
#[derive(Clone, Debug)]
pub struct FarkasCert {
    pub multipliers: Vec<Rat>,
}

impl LiaCertificate {
    /// Re-verify this certificate against the original DNF `disjuncts`. Returns `true`
    /// only when every disjunct's recorded refutation checks out by pure arithmetic /
    /// substitution. **This is the trusted checker**; it never calls back into the search.
    ///
    /// It fails (returns `false`) rather than panicking on any inconsistency — a wrong
    /// arity, an out-of-range multiplier, a non-contradictory combination, a claimed
    /// clash whose literals are absent, etc.
    pub fn check(&self, disjuncts: &[Vec<Literal>]) -> bool {
        if self.disjuncts.len() != disjuncts.len() {
            return false;
        }
        self.disjuncts
            .iter()
            .zip(disjuncts.iter())
            .all(|(cert, conj)| cert.check(conj))
    }
}

impl DisjunctCert {
    /// Check one disjunct's refutation against its literals.
    fn check(&self, conj: &[Literal]) -> bool {
        match self {
            DisjunctCert::OpaqueClash { atom } => check_opaque_clash(atom, conj),
            DisjunctCert::EqualityClash { asserted_eqs, diseq } => {
                check_equality_clash(asserted_eqs, diseq, conj)
            }
            DisjunctCert::LinearRefutation { branches } => check_linear(branches, conj),
        }
    }
}

/// Confirm `atom` genuinely appears both positively and negatively in `conj`.
fn check_opaque_clash(atom: &Atom, conj: &[Literal]) -> bool {
    let pos = conj.iter().any(|l| !l.negated && &l.atom == atom);
    let neg = conj.iter().any(|l| l.negated && &l.atom == atom);
    pos && neg
}

/// Confirm the recorded (dis)equalities are asserted and that the closure built from the
/// asserted equalities forces the disequality's sides equal.
fn check_equality_clash(
    asserted_eqs: &[(Term, Term)],
    diseq: &(Term, Term),
    conj: &[Literal],
) -> bool {
    for (l, r) in asserted_eqs {
        if !literal_asserts_cmp(conj, BinOp::Eq, l, r) {
            return false;
        }
    }
    if !literal_asserts_cmp(conj, BinOp::Ne, &diseq.0, &diseq.1) {
        return false;
    }
    let mut eq = EqClosure::new();
    for (l, r) in asserted_eqs {
        eq.assert_eq(l, r);
    }
    eq.see(&diseq.0);
    eq.see(&diseq.1);
    eq.close();
    eq.equal(&diseq.0, &diseq.1)
}

/// Is there a literal in `conj` whose *effective* comparison is `want` over `(l, r)`?
fn literal_asserts_cmp(conj: &[Literal], want: BinOp, l: &Term, r: &Term) -> bool {
    conj.iter().any(|lit| {
        let Atom::Cmp { op, lhs, rhs } = &lit.atom else { return false };
        if effective_cmp(*op, lit.negated) != Some(want) {
            return false;
        }
        (lhs == l && rhs == r) || (lhs == r && rhs == l)
    })
}

/// Re-derive the disjunct's linear constraints and disequalities from its literals,
/// enumerate the disequality-side branches in a fixed order, and confirm each branch's
/// Farkas certificate proves that branch UNSAT.
fn check_linear(branches: &[FarkasCert], conj: &[Literal]) -> bool {
    let Some((base, diseqs)) = reconstruct_linear(conj) else {
        return false;
    };
    let mut branch_constraints: Vec<Vec<LinConstraint>> = Vec::new();
    if !enumerate_branches(&base, &diseqs, 0, &mut branch_constraints) {
        return false;
    }
    if branch_constraints.len() != branches.len() {
        return false;
    }
    branch_constraints
        .iter()
        .zip(branches.iter())
        .all(|(constraints, cert)| check_farkas(cert, constraints))
}

/// Reconstruct, purely from the literals, the conjunction's base `≤ 0` constraints and
/// its disequalities — mirroring the solver's linear routing but *without* the search.
/// Returns `None` if any comparison overflows during normalization (then rejected — sound).
fn reconstruct_linear(conj: &[Literal]) -> Option<(Vec<LinConstraint>, Vec<Disequality>)> {
    let mut constraints = Vec::new();
    let mut disequalities = Vec::new();
    for lit in conj {
        let Atom::Cmp { op, lhs, rhs } = &lit.atom else { continue };
        if let Some(diseq) = cmp_to_disequality(*op, lhs, rhs, lit.negated) {
            disequalities.push(diseq);
            continue;
        }
        if let Some(mut cs) = cmp_to_constraints(*op, lhs, rhs, lit.negated) {
            constraints.append(&mut cs);
        }
    }
    Some((constraints, disequalities))
}

/// Depth-first enumeration of disequality-side combinations, appending each branch's full
/// constraint list (base ++ chosen sides) to `out`. Returns `false` on arithmetic overflow.
fn enumerate_branches(
    base: &[LinConstraint],
    diseqs: &[Disequality],
    idx: usize,
    out: &mut Vec<Vec<LinConstraint>>,
) -> bool {
    if idx == diseqs.len() {
        out.push(base.to_vec());
        return true;
    }
    let sides = diseqs[idx].sides();
    if sides.len() != 2 {
        return false;
    }
    for side in sides {
        let mut with_side = base.to_vec();
        with_side.push(side);
        if !enumerate_branches(&with_side, diseqs, idx + 1, out) {
            return false;
        }
    }
    true
}

/// Check a single Farkas certificate: form `Σ multipliers[i]·constraints[i].expr` with
/// all multipliers non-negative, and confirm the result is a strictly positive
/// variable-free constant. Pure arithmetic, no search.
fn check_farkas(cert: &FarkasCert, constraints: &[LinConstraint]) -> bool {
    if cert.multipliers.len() != constraints.len() {
        return false;
    }
    let mut acc = LinExpr::zero_expr();
    for (lambda, c) in cert.multipliers.iter().zip(constraints.iter()) {
        if !lambda.is_non_negative() {
            return false;
        }
        let Some(scaled) = c.expr().checked_scale(*lambda) else { return false };
        let Some(next) = acc.checked_add(&scaled) else { return false };
        acc = next;
    }
    acc.is_positive_constant()
}

#[cfg(test)]
mod tests {
    use super::*;
    use rv_core::{Symbols, Term};

    fn lit(atom: Atom, negated: bool) -> Literal {
        Literal { atom, negated }
    }
    fn cmp_atom(op: BinOp, l: Term, r: Term) -> Atom {
        Atom::Cmp { op, lhs: l, rhs: r }
    }
    fn v(s: &mut Symbols, name: &str) -> Term {
        Term::Var(s.intern(name))
    }

    // --- exact rationals ---------------------------------------------------

    #[test]
    fn rat_reduces_and_signs() {
        let r = Rat::new(4, -8).unwrap();
        assert_eq!(r, Rat { num: -1, den: 2 });
    }

    // --- propositional normalization (NNF / DNF) ---------------------------

    #[test]
    fn nnf_implies_becomes_or() {
        // a ⟹ b should NNF (un-negated) to ¬a ∨ b: an Or node.
        use rv_core::Prop;
        let mut s = Symbols::new();
        let a = Prop::Holds(Term::Var(s.intern("p")));
        let b = Prop::Holds(Term::Var(s.intern("q")));
        let imp = a.implies(b);
        let n = to_nnf(&imp, false);
        assert!(matches!(n, Nnf::Or(_, _)));
    }

    #[test]
    fn dnf_distributes() {
        // (p ∨ q) ∧ r  ⇒  (p ∧ r) ∨ (q ∧ r): two disjuncts.
        use rv_core::Prop;
        let mut s = Symbols::new();
        let p = Prop::Holds(Term::Var(s.intern("p")));
        let q = Prop::Holds(Term::Var(s.intern("q")));
        let r = Prop::Holds(Term::Var(s.intern("r")));
        let f = (p.or(q)).and(r);
        let n = to_nnf(&f, false);
        let d = dnf(&n, 100).unwrap();
        assert_eq!(d.len(), 2);
        for conj in &d {
            assert_eq!(conj.len(), 2);
        }
    }

    // --- equality / congruence closure -------------------------------------

    #[test]
    fn transitivity_holds() {
        let mut s = Symbols::new();
        let (a, b, c) = (v(&mut s, "a"), v(&mut s, "b"), v(&mut s, "c"));
        let mut uf = EqClosure::new();
        uf.assert_eq(&a, &b);
        uf.assert_eq(&b, &c);
        assert!(uf.equal(&a, &c));
    }

    #[test]
    fn symmetry_holds() {
        let mut s = Symbols::new();
        let (a, b) = (v(&mut s, "a"), v(&mut s, "b"));
        let mut uf = EqClosure::new();
        uf.assert_eq(&a, &b);
        assert!(uf.equal(&b, &a));
    }

    #[test]
    fn unrelated_not_equal() {
        let mut s = Symbols::new();
        let (a, b, c) = (v(&mut s, "a"), v(&mut s, "b"), v(&mut s, "c"));
        let mut uf = EqClosure::new();
        uf.assert_eq(&a, &b);
        assert!(!uf.equal(&a, &c));
    }

    /// Congruence: `a == b ⟹ f(a) == f(b)`.
    #[test]
    fn congruence_over_apps() {
        let mut s = Symbols::new();
        let (a, b) = (v(&mut s, "a"), v(&mut s, "b"));
        let f = s.intern("f");
        let fa = Term::app(f, vec![a.clone()]);
        let fb = Term::app(f, vec![b.clone()]);
        let mut uf = EqClosure::new();
        uf.assert_eq(&a, &b);
        uf.see(&fa);
        uf.see(&fb);
        uf.close();
        assert!(uf.equal(&fa, &fb));
    }

    /// Congruence does *not* over-fire: distinct, unequal arguments stay separate.
    #[test]
    fn no_spurious_congruence() {
        let mut s = Symbols::new();
        let (a, b) = (v(&mut s, "a"), v(&mut s, "b"));
        let f = s.intern("f");
        let fa = Term::app(f, vec![a.clone()]);
        let fb = Term::app(f, vec![b.clone()]);
        let mut uf = EqClosure::new();
        uf.see(&fa);
        uf.see(&fb);
        uf.close();
        assert!(!uf.equal(&fa, &fb));
    }

    /// Nested congruence to a fixpoint: `a == b ⟹ g(f(a)) == g(f(b))`.
    #[test]
    fn nested_congruence() {
        let mut s = Symbols::new();
        let (a, b) = (v(&mut s, "a"), v(&mut s, "b"));
        let (f, g) = (s.intern("f"), s.intern("g"));
        let gfa = Term::app(g, vec![Term::app(f, vec![a.clone()])]);
        let gfb = Term::app(g, vec![Term::app(f, vec![b.clone()])]);
        let mut uf = EqClosure::new();
        uf.assert_eq(&a, &b);
        uf.see(&gfa);
        uf.see(&gfb);
        uf.close();
        assert!(uf.equal(&gfa, &gfb));
    }

    // --- Farkas / clash checks ---------------------------------------------

    #[test]
    fn farkas_checks_simple_contradiction() {
        let mut s = Symbols::new();
        let x = Term::Var(s.intern("x"));
        let c1 = cmp_to_constraints(BinOp::Le, &x, &Term::Int(0), false).unwrap();
        let c2 = cmp_to_constraints(BinOp::Ge, &x, &Term::Int(1), false).unwrap();
        let mut all = c1;
        all.extend(c2);
        let cert = FarkasCert { multipliers: vec![Rat::from_int(1), Rat::from_int(1)] };
        assert!(check_farkas(&cert, &all));
    }

    #[test]
    fn farkas_rejects_non_contradiction() {
        let mut s = Symbols::new();
        let x = Term::Var(s.intern("x"));
        let c1 = cmp_to_constraints(BinOp::Le, &x, &Term::Int(0), false).unwrap();
        let c2 = cmp_to_constraints(BinOp::Ge, &x, &Term::Int(1), false).unwrap();
        let mut all = c1;
        all.extend(c2);
        let cert = FarkasCert { multipliers: vec![Rat::from_int(1), Rat::from_int(0)] };
        assert!(!check_farkas(&cert, &all));
    }

    #[test]
    fn farkas_rejects_negative_multiplier() {
        let mut s = Symbols::new();
        let x = Term::Var(s.intern("x"));
        let c1 = cmp_to_constraints(BinOp::Le, &x, &Term::Int(0), false).unwrap();
        let c2 = cmp_to_constraints(BinOp::Ge, &x, &Term::Int(1), false).unwrap();
        let mut all = c1;
        all.extend(c2);
        let cert = FarkasCert { multipliers: vec![Rat::from_int(-1), Rat::from_int(1)] };
        assert!(!check_farkas(&cert, &all));
    }

    #[test]
    fn opaque_clash_checks_and_rejects() {
        let atom = Atom::Opaque(OpaqueAtom::Term(Term::Bool(true)));
        let conj = vec![lit(atom.clone(), false), lit(atom.clone(), true)];
        assert!(check_opaque_clash(&atom, &conj));
        let conj2 = vec![lit(atom.clone(), false)];
        assert!(!check_opaque_clash(&atom, &conj2));
    }

    #[test]
    fn equality_clash_checks_and_rejects_fabrication() {
        let mut s = Symbols::new();
        let (a, b, d) = (s.intern("a"), s.intern("b"), s.intern("d"));
        let oa = Term::bin(BinOp::Div, Term::Var(a), Term::Var(d));
        let ob = Term::bin(BinOp::Div, Term::Var(b), Term::Var(d));
        let conj = vec![
            lit(cmp_atom(BinOp::Eq, oa.clone(), ob.clone()), false),
            lit(cmp_atom(BinOp::Ne, oa.clone(), ob.clone()), false),
        ];
        let good = DisjunctCert::EqualityClash {
            asserted_eqs: vec![(oa.clone(), ob.clone())],
            diseq: (oa.clone(), ob.clone()),
        };
        assert!(good.check(&conj));
        let oc = Term::bin(BinOp::Div, Term::Var(s.intern("c")), Term::Var(d));
        let fake = DisjunctCert::EqualityClash {
            asserted_eqs: vec![(oa.clone(), oc.clone())],
            diseq: (oa, oc),
        };
        assert!(!fake.check(&conj));
    }
}
