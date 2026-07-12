//! The linear-arithmetic **search**: Fourier–Motzkin elimination (with Farkas-multiplier
//! tracking) and a best-effort integer-model finder for counterexamples.
//!
//! The *checkable* data types — [`Rat`], [`LinExpr`], [`LinConstraint`], [`Disequality`],
//! and the pure `cmp_to_*` normalization — now live in [`rv_logic::lia`], because they
//! form the closed set the (trusted) certificate checker needs and must be re-runnable by
//! any consumer of an [`Outcome`](rv_logic::Outcome). What remains here is the *untrusted
//! search*: it produces certificates, but nothing here is trusted to be sound — a wrong
//! answer is caught downstream when [`rv_logic::LiaCertificate::check`] rejects the
//! emitted certificate.
//!
//! We decide satisfiability over the **rationals**; since rational-UNSAT implies
//! integer-UNSAT, proving a conjunction rational-UNSAT soundly proves it integer-UNSAT
//! (the only direction we rely on). Any arithmetic overflow is caught and reported as
//! "cannot decide" rather than wrapping.

use rv_core::Sym;
use rv_logic::{LinConstraint, LinExpr, Rat};
use std::collections::BTreeMap;

// Re-export the normalization the analyzer uses so `lib.rs` can keep referring to
// `linear::cmp_to_constraints` etc. unchanged — they are the pure functions in rv-logic.
pub use rv_logic::lia::{cmp_to_constraints, cmp_to_disequality, effective_cmp};
pub use rv_logic::Disequality;

// ===========================================================================
// Farkas certificate extraction (the core Fourier–Motzkin elimination)
// ===========================================================================

/// A row in the Farkas-tracking elimination: an expression `e ≤ 0` together with the
/// non-negative combination of the *original* constraints that produced it. `coeffs[i]`
/// is the multiplier applied to original constraint `i`. Invariant maintained
/// throughout elimination: `e == Σ coeffs[i] · original[i].expr` and every
/// `coeffs[i] ≥ 0`, so `e ≤ 0` is a sound consequence of the originals.
#[derive(Clone)]
struct FarkasRow {
    expr: LinExpr,
    coeffs: Vec<Rat>,
}

/// Decide whether a conjunction of `≤ 0` constraints is UNSAT over the rationals **and,
/// when it is, return a Farkas certificate**: a vector of non-negative rational
/// multipliers `λ`, one per input constraint, such that `Σ λᵢ · exprᵢ` is a
/// variable-free **strictly positive** constant. Returns `None` when it cannot prove
/// UNSAT (satisfiable, overflow, or otherwise undecided) — sound, we then claim nothing.
///
/// This is Fourier–Motzkin elimination, but each derived row additionally carries the
/// multiplier vector that produced it, so the contradicting constant row hands us its
/// Farkas coefficients directly — no search is re-run to *check* the result.
pub fn fourier_motzkin_farkas(constraints: &[LinConstraint]) -> Option<Vec<Rat>> {
    let n = constraints.len();
    // Seed: each original constraint is itself, with a unit multiplier on its own index.
    let mut rows: Vec<FarkasRow> = constraints
        .iter()
        .enumerate()
        .map(|(i, c)| {
            let mut coeffs = vec![Rat::zero_rat(); n];
            coeffs[i] = Rat::from_int(1);
            FarkasRow { expr: c.expr().clone(), coeffs }
        })
        .collect();

    if let Some(cert) = scan_farkas_constants(&mut rows) {
        return Some(cert);
    }

    while let Some(var) = pick_var_rows(&rows) {
        let mut pos: Vec<&FarkasRow> = Vec::new();
        let mut neg: Vec<&FarkasRow> = Vec::new();
        let mut rest: Vec<FarkasRow> = Vec::new();
        for row in &rows {
            let c = row.expr.coeff(var);
            if c.positive() {
                pos.push(row);
            } else if c.negative() {
                neg.push(row);
            } else {
                rest.push(row.clone());
            }
        }
        let mut next = rest;
        for p in &pos {
            for nn in &neg {
                match eliminate_farkas(p, nn, var) {
                    Some(combined) => next.push(combined),
                    None => return None,
                }
            }
        }
        rows = next;
        if let Some(cert) = scan_farkas_constants(&mut rows) {
            return Some(cert);
        }
    }
    // No variables left; a final scan finds any positive-constant contradiction.
    scan_farkas_constants(&mut rows)
}

/// Combine `α·p + β·n` (with `α = -cn > 0`, `β = cp > 0`) on both the expression and its
/// multiplier vector, preserving the invariant `expr == Σ coeffs[i]·original[i]`.
fn eliminate_farkas(p: &FarkasRow, n: &FarkasRow, var: Sym) -> Option<FarkasRow> {
    let cp = p.expr.coeff(var); // > 0
    let cn = n.expr.coeff(var); // < 0
    let alpha = cn.checked_neg()?; // > 0
    let beta = cp; // > 0
    let expr = p.expr.checked_scale(alpha)?.checked_add(&n.expr.checked_scale(beta)?)?;
    let mut coeffs = Vec::with_capacity(p.coeffs.len());
    for (pc, nc) in p.coeffs.iter().zip(n.coeffs.iter()) {
        coeffs.push(pc.checked_mul(alpha)?.checked_add(nc.checked_mul(beta)?)?);
    }
    Some(FarkasRow { expr, coeffs })
}

/// Scan rows for a variable-free strictly-positive constant (`c ≤ 0` with `c > 0`).
/// On finding one, return its multiplier vector — the Farkas certificate. Otherwise
/// drop trivially-true constant rows and return `None`.
fn scan_farkas_constants(rows: &mut Vec<FarkasRow>) -> Option<Vec<Rat>> {
    let drained = std::mem::take(rows);
    let mut kept = Vec::with_capacity(drained.len());
    for row in drained {
        if let Some(c) = row.expr.constant_value() {
            if c.positive() {
                *rows = kept;
                return Some(row.coeffs);
            }
        } else {
            kept.push(row);
        }
    }
    *rows = kept;
    None
}

/// Pick a variable still present in the Farkas rows (smallest `Sym`, deterministic).
fn pick_var_rows(rows: &[FarkasRow]) -> Option<Sym> {
    rows.iter().flat_map(|r| r.expr.var_syms()).min()
}

// ===========================================================================
// Counterexample search (best-effort integer model finding)
// ===========================================================================

/// Best-effort search for a concrete integer assignment satisfying a conjunction of
/// linear constraints (`expr ≤ 0`) and disequalities (`diff ≠ 0`), with every variable
/// ranged over the small box `[-BOX, BOX]`.
///
/// This is purely a *diagnostic* aid for `Outcome::Failed`; it never influences
/// soundness. Failing to find a model within the box does **not** mean none exists.
///
/// Returns the assignment as `(Sym, value)` pairs sorted by `Sym`, or `None`.
pub fn find_integer_model(
    constraints: &[LinConstraint],
    disequalities: &[Disequality],
) -> Option<Vec<(Sym, i64)>> {
    const BOX: i64 = 8;
    const MAX_VARS: usize = 5;

    let mut vars: Vec<Sym> = Vec::new();
    let mut see = |e: &LinExpr| {
        for s in e.var_syms() {
            if !vars.contains(&s) {
                vars.push(s);
            }
        }
    };
    for c in constraints {
        see(c.expr());
    }
    for d in disequalities {
        see(d.diff());
    }
    vars.sort();

    if vars.len() > MAX_VARS {
        return None;
    }

    let mut assign: BTreeMap<Sym, i64> = BTreeMap::new();

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

/// Does `assign` satisfy every `expr ≤ 0` constraint and every `diff ≠ 0` disequality?
fn satisfies_all(
    assign: &BTreeMap<Sym, i64>,
    constraints: &[LinConstraint],
    disequalities: &[Disequality],
) -> bool {
    for c in constraints {
        match rv_logic::lia::eval_lin(c.expr(), assign) {
            Some(v) if !rv_logic::lia::rat_is_positive(v) => {} // v ≤ 0 ✓
            _ => return false,
        }
    }
    for d in disequalities {
        match rv_logic::lia::eval_lin(d.diff(), assign) {
            Some(v) if !rv_logic::lia::rat_is_zero(v) => {} // diff ≠ 0 ✓
            _ => return false,
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use rv_core::{BinOp, Symbols, Term};

    fn v(s: &mut Symbols, name: &str) -> Term {
        Term::Var(s.intern(name))
    }

    #[test]
    fn fm_detects_simple_contradiction() {
        // x <= 0 AND x >= 1  (i.e. 1 - x <= 0)  is UNSAT.
        let mut s = Symbols::new();
        let x = v(&mut s, "x");
        let c1 = cmp_to_constraints(BinOp::Le, &x, &Term::Int(0), false).unwrap();
        let c2 = cmp_to_constraints(BinOp::Ge, &x, &Term::Int(1), false).unwrap();
        let mut all = c1;
        all.extend(c2);
        assert!(fourier_motzkin_farkas(&all).is_some());
    }

    #[test]
    fn fm_satisfiable_is_not_unsat() {
        let mut s = Symbols::new();
        let x = v(&mut s, "x");
        let c = cmp_to_constraints(BinOp::Ge, &x, &Term::Int(0), false).unwrap();
        assert!(fourier_motzkin_farkas(&c).is_none());
    }

    #[test]
    fn strict_lt_tightens_over_integers() {
        let mut s = Symbols::new();
        let x = v(&mut s, "x");
        let mut all = cmp_to_constraints(BinOp::Gt, &x, &Term::Int(3), false).unwrap();
        all.extend(cmp_to_constraints(BinOp::Le, &x, &Term::Int(3), false).unwrap());
        assert!(fourier_motzkin_farkas(&all).is_some());
    }

    #[test]
    fn non_linear_is_rejected() {
        let mut s = Symbols::new();
        let x = v(&mut s, "x");
        let y = v(&mut s, "y");
        let prod = Term::bin(BinOp::Mul, x, y);
        assert!(cmp_to_constraints(BinOp::Le, &prod, &Term::Int(0), false).is_none());
    }
}
