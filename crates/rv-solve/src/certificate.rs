//! Checkable unsatisfiability certificates for the linear-arithmetic + congruence
//! fragment — the machinery that moves `rv-solve`'s positive results out of the trust
//! base.
//!
//! # Why this exists
//!
//! [`LiaSolver`](crate) proves an obligation `ctx ⟹ goal` by refuting
//! `ctx ∧ ¬goal`: it enumerates that formula's DNF and shows **every** disjunct is
//! unsatisfiable. The refutation *search* (Fourier–Motzkin elimination, congruence
//! closure) is intricate; trusting it is trusting a lot of code. A **certificate**
//! records *just enough* of the proof that a small, obviously-sound [`check`](Certificate::check)
//! function can re-verify it by pure arithmetic and substitution — never re-running the
//! search. The search then becomes *untrusted*: if it emits a wrong certificate the
//! checker rejects it.
//!
//! # What a certificate contains
//!
//! A [`Certificate`] is a proof that a *whole* formula (a list of DNF disjuncts) is
//! unsatisfiable: one [`DisjunctCert`] per disjunct, since UNSAT of the disjunction
//! requires UNSAT of every disjunct. Each [`DisjunctCert`] is one of three sound
//! refutations of a single conjunction of literals:
//!
//! * [`DisjunctCert::OpaqueClash`] — an opaque atom asserted both positively and
//!   negatively (`p ∧ ¬p`). The checker confirms both literals are present.
//! * [`DisjunctCert::EqualityClash`] — a congruence-closure contradiction: a chain of
//!   asserted equalities forces `l = r`, yet `l ≠ r` is asserted. The checker replays
//!   the union–find from the recorded asserted equalities and confirms the clash.
//! * [`DisjunctCert::LinearRefutation`] — a **Farkas** refutation of the linear part.
//!   A disequality `a ≠ b` is a disjunction (`a < b ∨ a > b`); the disjunct is UNSAT
//!   only if it is UNSAT under *every* choice of side, so this carries one
//!   [`FarkasCert`] per side-combination branch.
//!
//! # The Farkas core
//!
//! After normalization every asserted comparison becomes some `≤ 0` constraints (`==`
//! contributes both directions; strict `<` tightens over the integers). A
//! [`FarkasCert`] is a vector of **non-negative** rational multipliers `λ`, one per
//! constraint. Checking is arithmetic with no search: form `Σ λᵢ · exprᵢ`; if the
//! result is a variable-free **strictly positive** constant then, because each summand
//! `λᵢ·(exprᵢ ≤ 0)` is a sound consequence of an asserted `≤ 0` fact, we have derived
//! `c ≤ 0` with `c > 0` — a manifest contradiction. That is the whole proof.
//!
//! # Independence of the checker
//!
//! [`Certificate::check`] takes only the *original DNF disjuncts* (the literals the
//! solver started from) and re-derives the normalized constraints itself via the same
//! pure `cmp_to_constraints` / `cmp_to_disequality` used during solving — which are
//! total, syntax-directed functions, not the search. It then does arithmetic. It calls
//! **nothing** in the Fourier–Motzkin engine or in `analyze_disjunct`. So a bug in the
//! search cannot make the checker accept an unsound certificate: at worst the search
//! emits a certificate the checker rejects.

use crate::linear::{self, LinConstraint, LinExpr, Rat};
use crate::normalize::{Atom, Literal};
use rv_core::{BinOp, Term};

/// A checkable proof that a formula (a list of DNF disjuncts of `ctx ∧ ¬goal`) is
/// unsatisfiable — i.e. that the obligation is valid. One [`DisjunctCert`] per disjunct.
#[derive(Clone, Debug)]
pub struct Certificate {
    /// One refutation per disjunct. The checker also verifies the *count* matches the
    /// disjuncts it is handed, so a certificate cannot silently skip a disjunct.
    pub disjuncts: Vec<DisjunctCert>,
}

/// A refutation of a single disjunct (a conjunction of literals).
#[derive(Clone, Debug)]
pub enum DisjunctCert {
    /// `p ∧ ¬p` for an opaque atom `p`. The checker confirms the atom appears both
    /// with `negated = false` and with `negated = true` in the disjunct's literals.
    OpaqueClash { atom: Atom },

    /// A congruence-closure contradiction. `asserted_eqs` are the `(l, r)` pairs the
    /// solver unioned; `diseq` is an asserted `(l, r)` whose sides those equalities
    /// force equal. The checker rebuilds the closure from `asserted_eqs` alone,
    /// confirms `diseq`'s sides are forced equal, and confirms both the equalities and
    /// the disequality are genuinely asserted by the disjunct.
    EqualityClash {
        asserted_eqs: Vec<(Term, Term)>,
        diseq: (Term, Term),
    },

    /// A Farkas refutation of the linear part. `branches` covers every combination of
    /// disequality sides; each branch must be linearly UNSAT. With no disequalities
    /// this is a single branch over the plain conjunction.
    LinearRefutation { branches: Vec<FarkasCert> },
}

/// A Farkas certificate for one linear branch: `multipliers[i]` is the non-negative
/// rational coefficient applied to the `i`-th `≤ 0` constraint of that branch (the
/// branch's constraint list is reconstructed by the checker in a fixed order, so a bare
/// vector suffices). The claim is that `Σ multipliers[i]·exprᵢ` is a positive constant.
#[derive(Clone, Debug)]
pub struct FarkasCert {
    pub multipliers: Vec<Rat>,
}

impl Certificate {
    /// Re-verify this certificate against the original DNF `disjuncts` (the literal
    /// lists the solver refuted). Returns `true` only when every disjunct's recorded
    /// refutation checks out by pure arithmetic / substitution. **This is the trusted
    /// checker**; it never calls back into the search.
    ///
    /// It fails (returns `false`) rather than panicking on any inconsistency — a wrong
    /// arity, an out-of-range multiplier, a non-contradictory combination, a claimed
    /// clash whose literals are absent, etc.
    pub fn check(&self, disjuncts: &[Vec<Literal>]) -> bool {
        // Every disjunct must be accounted for, exactly.
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

// ===========================================================================
// Opaque clash
// ===========================================================================

/// Confirm `atom` genuinely appears both positively and negatively in `conj`.
fn check_opaque_clash(atom: &Atom, conj: &[Literal]) -> bool {
    let pos = conj.iter().any(|l| !l.negated && &l.atom == atom);
    let neg = conj.iter().any(|l| l.negated && &l.atom == atom);
    pos && neg
}

// ===========================================================================
// Equality clash
// ===========================================================================

/// Confirm that (a) every recorded asserted equality is genuinely an asserted equality
/// literal of `conj`, (b) the recorded disequality is genuinely an asserted disequality
/// literal of `conj`, and (c) the closure built from the asserted equalities alone
/// forces the disequality's two sides into the same class. All three are required: (a)
/// and (b) keep the search from fabricating (dis)equalities; (c) is the actual
/// contradiction.
fn check_equality_clash(
    asserted_eqs: &[(Term, Term)],
    diseq: &(Term, Term),
    conj: &[Literal],
) -> bool {
    // (a) every asserted equality is present as an effective `==` literal.
    for (l, r) in asserted_eqs {
        if !literal_asserts_cmp(conj, BinOp::Eq, l, r) {
            return false;
        }
    }
    // (b) the disequality is present as an effective `!=` literal.
    if !literal_asserts_cmp(conj, BinOp::Ne, &diseq.0, &diseq.1) {
        return false;
    }
    // (c) rebuild the congruence closure from the asserted equalities and check the clash.
    let mut eq = crate::equality::EqClosure::new();
    for (l, r) in asserted_eqs {
        eq.assert_eq(l, r);
    }
    eq.see(&diseq.0);
    eq.see(&diseq.1);
    eq.close();
    eq.equal(&diseq.0, &diseq.1)
}

/// Is there a literal in `conj` whose *effective* comparison (folding in its `negated`
/// flag) is `want` over exactly `(l, r)`? Sides are compared by syntactic identity, in
/// order (the closure is symmetric, so order does not matter for soundness; we accept
/// either orientation to be robust to how the producer recorded it).
fn literal_asserts_cmp(conj: &[Literal], want: BinOp, l: &Term, r: &Term) -> bool {
    conj.iter().any(|lit| {
        let Atom::Cmp { op, lhs, rhs } = &lit.atom else { return false };
        if linear::effective_cmp(*op, lit.negated) != Some(want) {
            return false;
        }
        (lhs == l && rhs == r) || (lhs == r && rhs == l)
    })
}

// ===========================================================================
// Linear (Farkas) refutation
// ===========================================================================

/// Re-derive the disjunct's linear constraints and disequalities from its literals,
/// enumerate the disequality-side branches in the *same fixed order* the solver used,
/// and confirm each branch's Farkas certificate proves that branch UNSAT. Every branch
/// must be refuted (a disequality holds via one side *or* the other, so the conjunction
/// is UNSAT only if UNSAT under both).
fn check_linear(branches: &[FarkasCert], conj: &[Literal]) -> bool {
    let Some((base, diseqs)) = reconstruct_linear(conj) else {
        return false;
    };
    // Enumerate every side-combination: 2^k branches for k disequalities.
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
/// its disequalities — mirroring `analyze_disjunct`'s linear routing but *without* the
/// search. Returns `None` if any comparison overflows during normalization (then the
/// certificate cannot be checked, so it is rejected — sound).
///
/// Note we ignore opaque / equality-only literals here: a `LinearRefutation` claims the
/// contradiction is purely arithmetic, so only the linear literals matter. Opaque atoms
/// with consistent polarity are freely satisfiable and can never *help* a refutation.
fn reconstruct_linear(conj: &[Literal]) -> Option<(Vec<LinConstraint>, Vec<linear::Disequality>)> {
    let mut constraints = Vec::new();
    let mut disequalities = Vec::new();
    for lit in conj {
        let Atom::Cmp { op, lhs, rhs } = &lit.atom else { continue };
        if let Some(diseq) = linear::cmp_to_disequality(*op, lhs, rhs, lit.negated) {
            disequalities.push(diseq);
            continue;
        }
        // `cmp_to_constraints` returns None for non-linear or for `!=`; a `!=` was
        // already captured above, so a None here is simply a non-linear comparison,
        // which contributes nothing to a *linear* refutation. We must not silently drop
        // an arithmetic constraint, but a non-linear one is genuinely inert here.
        if let Some(mut cs) = linear::cmp_to_constraints(*op, lhs, rhs, lit.negated) {
            constraints.append(&mut cs);
        }
    }
    Some((constraints, disequalities))
}

/// Depth-first enumeration of disequality-side combinations, appending each branch's
/// full constraint list (base ++ chosen sides) to `out`. The traversal order — for each
/// disequality, its [`sides`](linear::Disequality::sides) in order, outer disequality
/// varying slowest — is exactly the order [`enumerate_branches`] itself and the solver
/// share, so branch `i` here corresponds to Farkas certificate `i`. Returns `false` on
/// arithmetic overflow while forming a side constraint.
fn enumerate_branches(
    base: &[LinConstraint],
    diseqs: &[linear::Disequality],
    idx: usize,
    out: &mut Vec<Vec<LinConstraint>>,
) -> bool {
    if idx == diseqs.len() {
        out.push(base.to_vec());
        return true;
    }
    let sides = diseqs[idx].sides();
    // `sides()` yields two constraints unless an overflow dropped one; a missing side
    // would make the enumeration unsound (we'd under-cover the disjunction), so reject.
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
/// variable-free constant (`c ≤ 0 ∧ c > 0` — false). Pure arithmetic, no search.
fn check_farkas(cert: &FarkasCert, constraints: &[LinConstraint]) -> bool {
    if cert.multipliers.len() != constraints.len() {
        return false;
    }
    let mut acc = LinExpr::zero_expr();
    for (lambda, c) in cert.multipliers.iter().zip(constraints.iter()) {
        // Farkas multipliers must be non-negative, or the combination is not a sound
        // consequence of the `≤ 0` constraints.
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
    use crate::normalize::{Atom, Literal, OpaqueAtom};
    use rv_core::{Symbols, Term};

    fn lit(atom: Atom, negated: bool) -> Literal {
        Literal { atom, negated }
    }
    fn cmp_atom(op: BinOp, l: Term, r: Term) -> Atom {
        Atom::Cmp { op, lhs: l, rhs: r }
    }

    // A Farkas certificate built and checked for `x ≤ 0 ∧ x ≥ 1`.
    #[test]
    fn farkas_checks_simple_contradiction() {
        let mut s = Symbols::new();
        let x = Term::Var(s.intern("x"));
        // x <= 0
        let c1 = linear::cmp_to_constraints(BinOp::Le, &x, &Term::Int(0), false).unwrap();
        // x >= 1  ⇒  1 - x <= 0
        let c2 = linear::cmp_to_constraints(BinOp::Ge, &x, &Term::Int(1), false).unwrap();
        let mut all = c1;
        all.extend(c2);
        // 1·(x) + 1·(1 - x) = 1 > 0.
        let cert = FarkasCert { multipliers: vec![Rat::from_int(1), Rat::from_int(1)] };
        assert!(check_farkas(&cert, &all));
    }

    // A tampered Farkas certificate (wrong coefficient) must be rejected.
    #[test]
    fn farkas_rejects_non_contradiction() {
        let mut s = Symbols::new();
        let x = Term::Var(s.intern("x"));
        let c1 = linear::cmp_to_constraints(BinOp::Le, &x, &Term::Int(0), false).unwrap();
        let c2 = linear::cmp_to_constraints(BinOp::Ge, &x, &Term::Int(1), false).unwrap();
        let mut all = c1;
        all.extend(c2);
        // 1·x + 0·(1-x) = x — not a positive constant (still has a variable).
        let cert = FarkasCert { multipliers: vec![Rat::from_int(1), Rat::from_int(0)] };
        assert!(!check_farkas(&cert, &all));
    }

    // A negative multiplier is not a valid Farkas coefficient.
    #[test]
    fn farkas_rejects_negative_multiplier() {
        let mut s = Symbols::new();
        let x = Term::Var(s.intern("x"));
        let c1 = linear::cmp_to_constraints(BinOp::Le, &x, &Term::Int(0), false).unwrap();
        let c2 = linear::cmp_to_constraints(BinOp::Ge, &x, &Term::Int(1), false).unwrap();
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
        // Only one polarity present ⇒ no clash.
        let conj2 = vec![lit(atom.clone(), false)];
        assert!(!check_opaque_clash(&atom, &conj2));
    }

    #[test]
    fn equality_clash_checks_and_rejects_fabrication() {
        let mut s = Symbols::new();
        let (a, b, d) = (s.intern("a"), s.intern("b"), s.intern("d"));
        let oa = Term::bin(BinOp::Div, Term::Var(a), Term::Var(d));
        let ob = Term::bin(BinOp::Div, Term::Var(b), Term::Var(d));
        // conj: a==b ∧ a!=b (opaque).
        let conj = vec![
            lit(cmp_atom(BinOp::Eq, oa.clone(), ob.clone()), false),
            lit(cmp_atom(BinOp::Ne, oa.clone(), ob.clone()), false),
        ];
        let good = DisjunctCert::EqualityClash {
            asserted_eqs: vec![(oa.clone(), ob.clone())],
            diseq: (oa.clone(), ob.clone()),
        };
        assert!(good.check(&conj));
        // Fabricated: claim an equality that isn't asserted in the disjunct.
        let oc = Term::bin(BinOp::Div, Term::Var(s.intern("c")), Term::Var(d));
        let fake = DisjunctCert::EqualityClash {
            asserted_eqs: vec![(oa.clone(), oc.clone())],
            diseq: (oa, oc),
        };
        assert!(!fake.check(&conj));
    }
}
