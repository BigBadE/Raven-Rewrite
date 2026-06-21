//! Linear arithmetic: expression normalization and Fourier–Motzkin elimination.
//!
//! A linear expression over integer variables is stored as a map from variable to
//! its (rational) coefficient, plus a rational constant. Constraints are kept in the
//! canonical form `expr ≤ 0`. We decide satisfiability over the **rationals**; since
//! rational-UNSAT implies integer-UNSAT, proving a conjunction rational-UNSAT
//! soundly proves it integer-UNSAT (the only direction we rely on).
//!
//! Rationals are exact (`i128` numerator / `i128` denominator, kept reduced and with
//! a positive denominator). Any arithmetic overflow is caught and reported as
//! "cannot decide" rather than wrapping — wrapping could be unsound.

use rv_core::{BinOp, Sym, Term, UnOp};
use std::collections::BTreeMap;

// ===========================================================================
// Exact rationals
// ===========================================================================

/// An exact rational `num/den`, kept reduced with `den > 0`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Rat {
    num: i128,
    den: i128,
}

impl Rat {
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
    fn int(n: i128) -> Rat {
        Rat { num: n, den: 1 }
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
    fn is_negative(&self) -> bool {
        self.num < 0
    }
    fn add(self, other: Rat) -> Option<Rat> {
        // a/b + c/d = (a*d + c*b) / (b*d)
        let n = self.num.checked_mul(other.den)?.checked_add(other.num.checked_mul(self.den)?)?;
        let d = self.den.checked_mul(other.den)?;
        Rat::new(n, d)
    }
    fn neg(self) -> Option<Rat> {
        Some(Rat { num: self.num.checked_neg()?, den: self.den })
    }
    fn mul(self, other: Rat) -> Option<Rat> {
        let n = self.num.checked_mul(other.num)?;
        let d = self.den.checked_mul(other.den)?;
        Rat::new(n, d)
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
/// A `BTreeMap` (ordered, deduped) keeps the representation canonical and the FM
/// elimination deterministic.
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
        m.insert(s, Rat::int(1));
        LinExpr { coeffs: m, constant: Rat::zero() }
    }

    fn add(&self, other: &LinExpr) -> Option<LinExpr> {
        let mut out = self.clone();
        out.constant = out.constant.add(other.constant)?;
        for (s, c) in &other.coeffs {
            let entry = out.coeffs.entry(*s).or_insert_with(Rat::zero);
            *entry = entry.add(*c)?;
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
    /// Scale by a rational constant.
    fn scale(&self, k: Rat) -> Option<LinExpr> {
        let mut out = LinExpr { coeffs: BTreeMap::new(), constant: self.constant.mul(k)? };
        for (s, c) in &self.coeffs {
            out.coeffs.insert(*s, c.mul(k)?);
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
}

/// Lower a `Term` to a linear expression, or `None` if it is not linear (e.g.
/// `Var*Var`, `Div`, `Mod`, or any overflow). `None` ⇒ the caller treats the
/// enclosing comparison as opaque, which is sound.
fn linearize(t: &Term) -> Option<LinExpr> {
    match t {
        Term::Int(n) => Some(LinExpr::constant(Rat::int(*n as i128))),
        Term::Var(s) => Some(LinExpr::var(*s)),
        Term::Bool(_) => None, // a boolean isn't an integer-linear value
        Term::Un(UnOp::Neg, a) => linearize(a)?.neg(),
        Term::Un(UnOp::Not, _) => None,
        // A field projection is opaque to linear arithmetic; the enclosing
        // comparison is treated as an atom (sound). Equality/congruence over
        // identical `Field` terms is what connects a spec's `p.v` to a code read.
        Term::Field(..) => None,
        // An uninterpreted application is opaque to linear arithmetic; the enclosing
        // comparison becomes an atom, and equality/congruence over `App` terms (in
        // the equality closure) is what connects two reads of the same function.
        Term::App(..) => None,
        Term::Bin(op, a, b) => match op {
            BinOp::Add => linearize(a)?.add(&linearize(b)?),
            BinOp::Sub => linearize(a)?.sub(&linearize(b)?),
            BinOp::Mul => {
                // Linear only if at least one side is a constant.
                let (la, lb) = (linearize(a)?, linearize(b)?);
                if let Some(k) = lb.as_constant() {
                    la.scale(k)
                } else if let Some(k) = la.as_constant() {
                    lb.scale(k)
                } else {
                    None // Var * Var — non-linear.
                }
            }
            // Div / Mod and all comparison/boolean ops are not linear arithmetic here.
            _ => None,
        },
    }
}

// ===========================================================================
// Constraints
// ===========================================================================

/// A single linear constraint in canonical form `expr ≤ 0`.
#[derive(Clone, Debug)]
pub struct LinConstraint {
    expr: LinExpr,
}

impl LinConstraint {
    /// `expr ≤ 0`.
    fn le_zero(expr: LinExpr) -> LinConstraint {
        LinConstraint { expr }
    }
}

/// A disequality `lhs ≠ rhs` over linear expressions, stored as `diff = lhs - rhs`.
/// It is equivalent to the disjunction `diff < 0 ∨ diff > 0`, i.e. (over integers)
/// `diff ≤ -1  ∨  diff ≥ 1`. The caller branches over [`Self::sides`].
#[derive(Clone, Debug)]
pub struct Disequality {
    diff: LinExpr, // lhs - rhs
}

impl Disequality {
    /// The two `≤ 0` constraints, one per side of the disjunction:
    /// * `lhs < rhs`  ⇒  `diff ≤ -1`  ⇒  `diff + 1 ≤ 0`;
    /// * `lhs > rhs`  ⇒  `diff ≥ 1`   ⇒  `1 - diff ≤ 0`  ⇒  `-diff + 1 ≤ 0`.
    ///
    /// Both directions use integrality (the `±1` tightening), which is sound.
    pub fn sides(&self) -> Vec<LinConstraint> {
        let mut out = Vec::new();
        // diff + 1 ≤ 0
        if let Some(lt) = self.diff.add(&LinExpr::constant(Rat::int(1))) {
            out.push(LinConstraint::le_zero(lt));
        }
        // -diff + 1 ≤ 0
        if let Some(neg) = self.diff.neg() {
            if let Some(gt) = neg.add(&LinExpr::constant(Rat::int(1))) {
                out.push(LinConstraint::le_zero(gt));
            }
        }
        out
    }
}

/// If `lhs op rhs` (after absorbing `negated`) is a **disequality** `≠` over linear
/// expressions, return it; otherwise `None`. `None` does not imply the comparison is
/// unusable — only that it is not a disequality (it may still be an `≤/==` constraint
/// handled by [`cmp_to_constraints`]).
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

/// Translate a (possibly negated) integer comparison `lhs op rhs` into an
/// equivalent **set** of `≤ 0` constraints, or `None` if either side isn't linear
/// **or** the comparison is a disequality.
///
/// The whole conjunction's constraints are AND-ed, so returning several constraints
/// here expresses an `AND` (e.g. `==` ⇒ both `≤` directions). A disequality `≠` is
/// naturally a *disjunction* and cannot be expressed as a conjunction, so it is **not**
/// handled here — the caller routes it through [`cmp_to_disequality`] and branches
/// over the two sides instead. Hence `Ne` (and negated `==`) return `None` here.
///
/// Integer strictness: `a < b ⟺ a ≤ b − 1` and `a > b ⟺ a ≥ b + 1`. This is the
/// one place we *use* integrality, and it only ever tightens a constraint, so it is
/// sound.
pub fn cmp_to_constraints(
    op: BinOp,
    lhs: &Term,
    rhs: &Term,
    negated: bool,
) -> Option<Vec<LinConstraint>> {
    // Effective operator after absorbing the literal's polarity.
    // ¬(a == b) = a != b ; ¬(a < b) = a >= b ; etc.
    let eff = if negated { negate_cmp(op)? } else { op };

    let l = linearize(lhs)?;
    let r = linearize(rhs)?;

    match eff {
        // a <= b  ⇒  a - b <= 0
        BinOp::Le => Some(vec![LinConstraint::le_zero(l.sub(&r)?)]),
        // a >= b  ⇒  b - a <= 0
        BinOp::Ge => Some(vec![LinConstraint::le_zero(r.sub(&l)?)]),
        // a < b   ⇒  a - b + 1 <= 0   (integers)
        BinOp::Lt => {
            let e = l.sub(&r)?.add(&LinExpr::constant(Rat::int(1)))?;
            Some(vec![LinConstraint::le_zero(e)])
        }
        // a > b   ⇒  b - a + 1 <= 0   (integers)
        BinOp::Gt => {
            let e = r.sub(&l)?.add(&LinExpr::constant(Rat::int(1)))?;
            Some(vec![LinConstraint::le_zero(e)])
        }
        // a == b  ⇒  a - b <= 0  AND  b - a <= 0
        BinOp::Eq => {
            Some(vec![LinConstraint::le_zero(l.sub(&r)?), LinConstraint::le_zero(r.sub(&l)?)])
        }
        // a != b is a disjunction handled by `cmp_to_disequality`, not here.
        BinOp::Ne => None,
        _ => None,
    }
}

/// The effective comparison operator after absorbing a literal's `negated` flag.
/// `None` if `op` is not a comparison. Used by the equality layer to decide whether
/// an *opaque* comparison is an asserted `==` (effective `Eq`) or `!=` (effective
/// `Ne`) once the literal's polarity is folded in.
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
// Fourier–Motzkin elimination
// ===========================================================================

/// Decide whether a conjunction of `≤ 0` constraints is **unsatisfiable over the
/// rationals**. Returns `true` only when proven UNSAT. Any overflow or other
/// inability to decide returns `false` (sound: we then don't claim UNSAT).
///
/// Algorithm: repeatedly pick a variable and eliminate it. For each pair of a
/// constraint with a positive coefficient and one with a negative coefficient on
/// that variable, form their positive combination (which cancels the variable). When
/// no variables remain, every constraint is a constant `c ≤ 0`; if any has `c > 0`
/// the system is contradictory ⇒ UNSAT.
pub fn fourier_motzkin_unsat(constraints: &[LinConstraint]) -> bool {
    // Work on owned expressions; each represents `expr ≤ 0`.
    let mut rows: Vec<LinExpr> = constraints.iter().map(|c| c.expr.clone()).collect();

    // Check any constraints that are already variable-free for an immediate
    // contradiction, and drop trivially-true ones (`c ≤ 0` with c ≤ 0).
    if let Some(contra) = scan_constants(&mut rows) {
        return contra; // true ⇒ found `c > 0 ≤ 0`, i.e. UNSAT.
    }

    // Eliminate variables one at a time.
    while let Some(var) = pick_var(&rows) {
        let mut pos: Vec<&LinExpr> = Vec::new(); // coeff(var) > 0
        let mut neg: Vec<&LinExpr> = Vec::new(); // coeff(var) < 0
        let mut rest: Vec<LinExpr> = Vec::new(); // coeff(var) == 0

        for row in &rows {
            match row.coeffs.get(&var).copied() {
                Some(c) if c.is_positive() => pos.push(row),
                Some(c) if c.is_negative() => neg.push(row),
                _ => rest.push(row.clone()),
            }
        }

        // Combine each positive/negative pair to cancel `var`.
        let mut next = rest;
        for p in &pos {
            for n in &neg {
                match eliminate(p, n, var) {
                    Some(combined) => next.push(combined),
                    // Overflow or arithmetic failure ⇒ we cannot soundly continue.
                    None => return false,
                }
            }
        }
        rows = next;

        // A fresh batch of constant rows may have appeared; check them.
        if let Some(contra) = scan_constants(&mut rows) {
            return contra;
        }
    }

    // No variables left. Re-scan; any leftover `c ≤ 0` with c > 0 is a contradiction.
    scan_constants(&mut rows).unwrap_or(false)
}

/// Eliminate `var` from the pair `p` (positive coeff) and `n` (negative coeff) by
/// forming a non-negative combination `αp + βn` whose `var` coefficient is zero.
/// Both `α, β > 0`, so `(αp ≤ 0) + (βn ≤ 0)` is a sound consequence.
fn eliminate(p: &LinExpr, n: &LinExpr, var: Sym) -> Option<LinExpr> {
    let cp = *p.coeffs.get(&var)?; // > 0
    let cn = *n.coeffs.get(&var)?; // < 0
                                   // We want α·cp + β·cn = 0 with α,β > 0. Take α = -cn (>0), β = cp (>0).
    let alpha = cn.neg()?; // > 0
    let beta = cp; // > 0
    let combined = p.scale(alpha)?.add(&n.scale(beta)?)?;
    Some(combined)
}

/// Inspect variable-free rows. Returns:
/// * `Some(true)`  — found a contradiction `c ≤ 0` with `c > 0` ⇒ system UNSAT;
/// * `None`        — no contradiction; (trivially-true constant rows are removed).
///
/// Rows that still have variables are left untouched.
fn scan_constants(rows: &mut Vec<LinExpr>) -> Option<bool> {
    let drained: Vec<LinExpr> = std::mem::take(rows);
    let mut kept = Vec::with_capacity(drained.len());
    for row in drained {
        if let Some(c) = row.as_constant() {
            if c.is_positive() {
                // `c ≤ 0` with c > 0 is false ⇒ contradiction. Restore the kept rows
                // for caller cleanliness, then signal UNSAT.
                *rows = kept;
                return Some(true);
            }
            // c ≤ 0 holds — a trivially satisfied constraint; drop it.
        } else {
            kept.push(row);
        }
    }
    *rows = kept;
    None
}

/// Pick some variable still present in the rows (deterministically: the smallest
/// `Sym`, since rows use a `BTreeMap`).
fn pick_var(rows: &[LinExpr]) -> Option<Sym> {
    rows.iter().flat_map(|r| r.coeffs.keys().copied()).min()
}

// ===========================================================================
// Counterexample search (best-effort integer model finding)
// ===========================================================================

/// Best-effort search for a concrete integer assignment satisfying a conjunction of
/// linear constraints (`expr ≤ 0`) and disequalities (`diff ≠ 0`), with every
/// variable ranged over the small box `[-BOX, BOX]`.
///
/// This is purely a *diagnostic* aid for `Outcome::Failed`: it never influences
/// soundness. If it finds a model it is genuinely a model of the linear part (we
/// evaluate the exact rationals), but failing to find one within the box does **not**
/// mean none exists — callers must treat absence of a model as "no counterexample
/// reported", not as proof of unsatisfiability.
///
/// Returns the assignment as `(Sym, value)` pairs sorted by `Sym`, or `None` if no
/// assignment in the box satisfies all constraints (or the search would be too large).
pub fn find_integer_model(
    constraints: &[LinConstraint],
    disequalities: &[Disequality],
) -> Option<Vec<(Sym, i64)>> {
    const BOX: i64 = 8;
    // Total candidate variables guard: with a small box, cap the search dimension so
    // we never explode. (17^5 ≈ 1.4M evaluations is plenty for this slice.)
    const MAX_VARS: usize = 5;

    // Collect every variable appearing in any constraint or disequality.
    let mut vars: Vec<Sym> = Vec::new();
    let see = |e: &LinExpr, vars: &mut Vec<Sym>| {
        for s in e.coeffs.keys() {
            if !vars.contains(s) {
                vars.push(*s);
            }
        }
    };
    for c in constraints {
        see(&c.expr, &mut vars);
    }
    for d in disequalities {
        see(&d.diff, &mut vars);
    }
    vars.sort();

    if vars.len() > MAX_VARS {
        return None;
    }

    // If there are no variables at all, the "model" is empty; it's valid iff every
    // constant constraint holds.
    let mut assign: BTreeMap<Sym, i64> = BTreeMap::new();

    // Odometer over the box for each variable.
    let dim = vars.len();
    let span = 2 * BOX + 1;
    let total = (0..dim).try_fold(1i64, |acc, _| acc.checked_mul(span))?;

    for n in 0..total {
        let mut rem = n;
        for &x in &vars {
            let digit = rem % span;
            rem /= span;
            assign.insert(x, digit - BOX);
        }
        if satisfies_all(&assign, constraints, disequalities) {
            return Some(vars.iter().map(|s| (*s, assign[s])).collect());
        }
        if dim == 0 {
            break; // single trivial point
        }
    }
    None
}

/// Evaluate a `LinExpr` at an integer assignment, returning the exact rational value
/// (variables not in `assign` are treated as 0 — they never occur here because the
/// search assigns every variable that appears).
fn eval(e: &LinExpr, assign: &BTreeMap<Sym, i64>) -> Option<Rat> {
    let mut acc = e.constant;
    for (s, c) in &e.coeffs {
        let val = Rat::int(*assign.get(s).unwrap_or(&0) as i128);
        acc = acc.add(c.mul(val)?)?;
    }
    Some(acc)
}

/// Does `assign` satisfy every `expr ≤ 0` constraint and every `diff ≠ 0` disequality?
fn satisfies_all(
    assign: &BTreeMap<Sym, i64>,
    constraints: &[LinConstraint],
    disequalities: &[Disequality],
) -> bool {
    for c in constraints {
        match eval(&c.expr, assign) {
            Some(v) if !v.is_positive() => {} // v ≤ 0 ✓
            _ => return false,
        }
    }
    for d in disequalities {
        match eval(&d.diff, assign) {
            Some(v) if !v.is_zero() => {} // diff ≠ 0 ✓
            _ => return false,
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use rv_core::Symbols;

    fn v(s: &mut Symbols, name: &str) -> Term {
        Term::Var(s.intern(name))
    }

    #[test]
    fn rat_reduces_and_signs() {
        let r = Rat::new(4, -8).unwrap();
        assert_eq!(r, Rat { num: -1, den: 2 });
    }

    #[test]
    fn fm_detects_simple_contradiction() {
        // x <= 0 AND x >= 1  (i.e. 1 - x <= 0)  is UNSAT.
        let mut s = Symbols::new();
        let x = v(&mut s, "x");
        // x <= 0
        let c1 = cmp_to_constraints(BinOp::Le, &x, &Term::Int(0), false).unwrap();
        // x >= 1
        let c2 = cmp_to_constraints(BinOp::Ge, &x, &Term::Int(1), false).unwrap();
        let mut all = c1;
        all.extend(c2);
        assert!(fourier_motzkin_unsat(&all));
    }

    #[test]
    fn fm_satisfiable_is_not_unsat() {
        // x >= 0  alone is satisfiable.
        let mut s = Symbols::new();
        let x = v(&mut s, "x");
        let c = cmp_to_constraints(BinOp::Ge, &x, &Term::Int(0), false).unwrap();
        assert!(!fourier_motzkin_unsat(&c));
    }

    #[test]
    fn strict_lt_tightens_over_integers() {
        // 3 < x < 5  forces x == 4, so adding x != 4's "x <= 4 AND x >= 4" is fine,
        // but more basically: 3 < x AND x < 5 AND x <= 3 should be UNSAT
        // (x>3 ⇒ x>=4 contradicts x<=3).
        let mut s = Symbols::new();
        let x = v(&mut s, "x");
        let mut all = cmp_to_constraints(BinOp::Gt, &x, &Term::Int(3), false).unwrap();
        all.extend(cmp_to_constraints(BinOp::Le, &x, &Term::Int(3), false).unwrap());
        assert!(fourier_motzkin_unsat(&all));
    }

    #[test]
    fn non_linear_is_rejected() {
        // x * y is not linear ⇒ linearize returns None ⇒ cmp is opaque.
        let mut s = Symbols::new();
        let x = v(&mut s, "x");
        let y = v(&mut s, "y");
        let prod = Term::bin(BinOp::Mul, x, y);
        assert!(cmp_to_constraints(BinOp::Le, &prod, &Term::Int(0), false).is_none());
    }
}
