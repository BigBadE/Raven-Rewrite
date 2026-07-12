//! Built-in decision procedures that discharge verification obligations.
//!
//! # What this crate proves
//!
//! An [`Obligation`] asks whether `ctx ⟹ goal` is **valid** (true under every
//! assignment to its variables). Equivalently — and this is the form we actually
//! decide — whether `ctx ∧ ¬goal` is **unsatisfiable**.
//!
//! This crate is *trust-base adjacent* (see `ARCHITECTURE.md`). The structural
//! fast-path emits replay certificates that `rv-logic` validates independently;
//! the linear arithmetic engine remains **trusted** until it emits a checkable
//! unsatisfiability certificate. Therefore the overriding invariant is:
//!
//! > **SOUNDNESS:** we return [`Outcome::Discharged`] only when the obligation is
//! > genuinely valid. When we cannot *prove* validity we return
//! > [`Outcome::Failed`]. We are deliberately **incomplete**: there are valid
//! > obligations we give up on. That is acceptable; an unsound `Discharged` is not.
//!
//! # The fragment we decide
//!
//! * Propositional structure over `Prop`: `True / False / Not / And / Or / Implies`,
//!   plus `Holds(term)` where `term` is a boolean-valued [`Term`].
//! * Inside a `Holds`, boolean structure (`And / Or / Not`, bool literals) and integer
//!   comparisons (`Eq / Ne / Lt / Le / Gt / Ge`) are understood.
//! * Linear integer arithmetic over terms: `Int` literals, `Var`, `Add`, `Sub`,
//!   `Neg`, and `Mul` **only when one side is a constant** (so the result stays
//!   linear). Anything non-linear (`Var * Var`, `Div`/`Mod`, `Forall`/`Exists`)
//!   becomes an **opaque atom**: an uninterpreted boolean we treat only by syntactic
//!   identity. Opaque atoms are sound — they are simply unconstrained, which can only
//!   make us *fail* to prove a goal, never falsely prove one.
//!
//! # The method
//!
//! 1. Build `ctx ∧ ¬goal`, push negations to the leaves (NNF).
//! 2. Enumerate its DNF: a disjunction of conjunctions of literals. The whole
//!    formula is UNSAT iff **every** disjunct is UNSAT. (DNF can blow up; we guard
//!    with a size limit and `Failed`-out if exceeded — sound, just incomplete.)
//! 3. Each disjunct is a conjunction of atomic literals. Split it into:
//!    * **linear constraints** (comparisons), normalized to `Σ cᵢ·xᵢ + k  ⋈  0`, then
//!      reduced to non-strict `≤ 0` constraints over the **rationals** (strict `<`
//!      over integers tightens: `a < b ⟺ a ≤ b − 1`);
//!    * **opaque literals** `p` / `¬p`.
//!
//!    A disjunct is UNSAT if the opaque part is contradictory (`p ∧ ¬p`) **or** the
//!    linear part is rational-UNSAT (decided by Fourier–Motzkin elimination).
//!    Rational-UNSAT implies integer-UNSAT, so this direction is sound.
//! 4. All disjuncts UNSAT ⇒ `Discharged`. Otherwise `Failed`.
//!
//! # The equality / congruence fragment
//!
//! Comparisons whose operands are **not** linear integer expressions (e.g. over
//! `Div`/`Mod` terms) are not thrown away as inert opaque atoms when they are `==`
//! or `!=`: they feed an equality closure (a union–find, see [`equality`]) so the
//! equality theory still applies. Within a disjunct:
//!
//! * every asserted opaque `l == r` unions `l` and `r`;
//! * the disjunct is UNSAT if any asserted opaque `l != r` has `l` and `r` already
//!   in the same class (forced equal yet asserted unequal). This makes
//!   `a == b ∧ b == c ⟹ a == c`, `a == b ⟹ b == a`, and `a == b ∧ a != b ⟹ ⊥`
//!   provable even when `a`, `b`, `c` are uninterpreted. We do **not** model function
//!   symbols, so `a == b ⟹ f(a) == f(b)` stays out of scope (and unproved).
//!
//! Soundness of this layer is argued in [`equality`]: it only ever reports UNSAT on a
//! direct equality-vs-disequality contradiction, which is a genuine consequence of
//! the asserted (dis)equalities.
//!
//! # Counterexamples (diagnostics only)
//!
//! When a disjunct is *not* refuted, its linear part is satisfiable (over the
//! rationals, and frequently over the integers). As a best-effort aid we search a
//! small integer box (each variable in `[-8, 8]`) for a concrete satisfying
//! assignment and, if found, surface it in `Outcome::Failed(Some("counterexample: …"))`.
//! This never affects soundness: it only annotates failures. A failure with no model
//! string simply means none was found in the box — not that the obligation is valid.

use rv_core::Prop;
use rv_logic::{Certificate, Obligation, Outcome, ReplayCertificate, Solver, SolverRegistry};

mod certificate;
mod equality;
mod linear;
mod normalize;

pub use certificate::{Certificate as UnsatCertificate, DisjunctCert, FarkasCert};
pub use normalize::{Atom, Literal, OpaqueAtom};

use certificate::Certificate as UnsatCert;
use equality::EqClosure;
use linear::{Disequality, LinConstraint};

/// Build a registry preloaded with the built-in solvers, ready to `.discharge(&ob)`.
///
/// The trivial fast-path runs first (cheap, catches tautologies and `False` in the
/// context); the linear-integer-arithmetic prover runs second.
pub fn default_registry() -> SolverRegistry {
    let mut reg = SolverRegistry::new();
    reg.register(Box::new(TrivialSolver));
    reg.register(Box::new(LiaSolver));
    reg
}

// ===========================================================================
// Trivial fast-path solver
// ===========================================================================

/// Cheap structural discharges that don't need the arithmetic engine:
/// * the goal is literally `True`;
/// * the context literally contains `False` (anything follows from falsehood);
/// * the goal appears syntactically as a top-level conjunct of the context.
///
/// All three are obviously sound. This solver never claims anything subtler.
struct TrivialSolver;

impl Solver for TrivialSolver {
    fn name(&self) -> &'static str {
        "trivial"
    }

    fn try_solve(&self, ob: &Obligation) -> Outcome {
        // goal == True  ⇒  valid.
        if matches!(ob.goal, Prop::True) {
            return Outcome::Discharged(Certificate::Replay(ReplayCertificate::GoalTrue));
        }
        // False is a top-level conjunct of ctx  ⇒  ctx is unsatisfiable, so
        // `ctx ⟹ anything` is valid.
        if context_contains_false(&ob.ctx) {
            return Outcome::Discharged(Certificate::Replay(
                ReplayCertificate::ContextContainsFalse,
            ));
        }
        // goal is one of the top-level conjuncts of ctx  ⇒  valid (`H ∧ … ⟹ H`).
        if conjuncts_contain(&ob.ctx, &ob.goal) {
            return Outcome::Discharged(Certificate::Replay(
                ReplayCertificate::ContextContainsGoal,
            ));
        }
        Outcome::Failed(None)
    }
}

/// True if `False` appears as a top-level conjunct of `p`.
fn context_contains_false(p: &Prop) -> bool {
    match p {
        Prop::False => true,
        Prop::And(a, b) => context_contains_false(a) || context_contains_false(b),
        _ => false,
    }
}

/// True if `goal` is syntactically equal to one of the top-level conjuncts of `ctx`.
fn conjuncts_contain(ctx: &Prop, goal: &Prop) -> bool {
    match ctx {
        Prop::And(a, b) => conjuncts_contain(a, goal) || conjuncts_contain(b, goal),
        other => other == goal,
    }
}

// ===========================================================================
// Linear-integer-arithmetic solver
// ===========================================================================

/// Above this many disjuncts in the enumerated DNF we give up (return `Failed`).
/// DNF size is worst-case exponential; this slice's formulas are tiny, so a
/// generous-but-finite cap keeps us from pathological blow-up while staying sound.
const MAX_DISJUNCTS: usize = 4096;

/// The linear-arithmetic + opaque-atom prover described in the module docs.
struct LiaSolver;

impl Solver for LiaSolver {
    fn name(&self) -> &'static str {
        "lia"
    }

    fn try_solve(&self, ob: &Obligation) -> Outcome {
        match prove(ob) {
            // We produced a checkable certificate. Self-check it before trusting our own
            // verdict: this is the whole point — the (untrusted) search's answer is only
            // accepted once the (trusted) checker re-verifies the emitted certificate
            // against the original disjuncts. A failed self-check is a solver bug; we
            // conservatively report `Failed` rather than an unchecked `Discharged`.
            ProveResult::Unsat { certificate, disjuncts } => {
                if certificate.check(&disjuncts) {
                    Outcome::Discharged(Certificate::trusted("lia"))
                } else {
                    Outcome::Failed(Some(
                        "internal: emitted certificate failed self-check".into(),
                    ))
                }
            }
            ProveResult::Unknown(msg) => Outcome::Failed(msg),
        }
    }
}

/// The result of the (untrusted) refutation search over `ctx ∧ ¬goal`.
enum ProveResult {
    /// Every disjunct was refuted. Carries the checkable [`UnsatCert`] and the exact
    /// `disjuncts` it was built against (so the checker has both halves).
    Unsat { certificate: UnsatCert, disjuncts: Vec<Vec<Literal>> },
    /// We could not refute some disjunct (satisfiable, too large, or undecidable);
    /// carries an optional diagnostic/counterexample message.
    Unknown(Option<String>),
}

/// Run the refutation search for `ctx ⟹ goal` and, on success, produce a checkable
/// certificate. This is the untrusted engine behind both [`LiaSolver`] and the public
/// [`prove_with_certificate`].
fn prove(ob: &Obligation) -> ProveResult {
    // We prove `ctx ⟹ goal` by refuting `ctx ∧ ¬goal`.
    let formula =
        Prop::And(Box::new(ob.ctx.clone()), Box::new(Prop::Not(Box::new(ob.goal.clone()))));

    // Push negations to the leaves (NNF), then enumerate the DNF as a list of
    // conjunctions-of-literals. `dnf` returns None if it overflows the cap.
    let nnf = normalize::to_nnf(&formula, false);
    let disjuncts = match normalize::dnf(&nnf, MAX_DISJUNCTS) {
        Some(d) => d,
        None => return ProveResult::Unknown(Some("formula too large for DNF enumeration".into())),
    };

    // The formula is UNSAT iff every disjunct is UNSAT. Collect one certificate per
    // disjunct; if any disjunct is satisfiable (or unrefutable) the obligation is not
    // proved — and we try to extract a concrete counterexample from that disjunct.
    let mut disjunct_certs = Vec::with_capacity(disjuncts.len());
    for conj in &disjuncts {
        match analyze_disjunct(conj) {
            DisjunctVerdict::Unsat(cert) => disjunct_certs.push(cert),
            DisjunctVerdict::Sat { constraints, disequalities } => {
                // Best-effort: search a small integer box for a model of the linear part
                // of this satisfiable disjunct.
                let msg = match linear::find_integer_model(&constraints, &disequalities) {
                    Some(model) => format!("counterexample: {}", render_model(&model)),
                    None => "could not refute a case (possible counterexample)".into(),
                };
                return ProveResult::Unknown(Some(msg));
            }
        }
    }
    ProveResult::Unsat {
        certificate: UnsatCert { disjuncts: disjunct_certs },
        disjuncts,
    }
}

/// Public API: attempt to prove `ctx ⟹ goal` and, on success, return a checkable unsat
/// [`UnsatCertificate`](certificate::Certificate) **together with the DNF disjuncts it
/// is proven against** — the pair [`UnsatCertificate::check`](certificate::Certificate::check)
/// expects. Returns `None` when the obligation could not be refuted.
///
/// The certificate is independently re-verifiable: `cert.check(&disjuncts)` re-derives
/// every constraint from the literals and re-checks by pure arithmetic, calling nothing
/// in the search. See [`check_certificate`] for the convenience wrapper.
pub fn prove_with_certificate(
    ob: &Obligation,
) -> Option<(certificate::Certificate, Vec<Vec<Literal>>)> {
    match prove(ob) {
        ProveResult::Unsat { certificate, disjuncts } => Some((certificate, disjuncts)),
        ProveResult::Unknown(_) => None,
    }
}

/// Public API: re-verify a certificate against the disjuncts it claims to refute. This
/// is the tiny trusted checker; it performs only arithmetic and substitution.
pub fn check_certificate(cert: &certificate::Certificate, disjuncts: &[Vec<Literal>]) -> bool {
    cert.check(disjuncts)
}

/// Render a `(Sym, value)` model as a human-readable assignment string. Symbols are
/// printed by their numeric id (the solver has no access to the `Symbols` table here)
/// in the deterministic order the model was produced, e.g. `x#0=0, x#1=-3`.
fn render_model(model: &[(rv_core::Sym, i64)]) -> String {
    if model.is_empty() {
        return "(no free variables)".into();
    }
    model
        .iter()
        .map(|(s, v)| format!("v{}={}", s.0, v))
        .collect::<Vec<_>>()
        .join(", ")
}

/// The result of analyzing one disjunct: either proven UNSAT, or possibly-SAT with the
/// linear part exposed so the caller can hunt for a counterexample model.
enum DisjunctVerdict {
    Unsat(DisjunctCert),
    Sat { constraints: Vec<LinConstraint>, disequalities: Vec<Disequality> },
}

/// Analyze a single conjunction of literals: prove it UNSAT, or report it as
/// possibly-SAT (exposing the linear part for counterexample search).
///
/// We return [`DisjunctVerdict::Unsat`] only when we can *prove* unsatisfiability via
/// one of three sound checks:
/// * an opaque atom and its negation both appear (`p ∧ ¬p`);
/// * the equality closure forces `l = r` while `l ≠ r` is asserted;
/// * the linear part is rational-UNSAT (Fourier–Motzkin) under every disequality
///   branch.
///
/// If a literal falls outside the linear fragment we demote it: opaque `==`/`!=` go
/// to the equality closure, everything else to bare opaque atoms. If none of the
/// checks fire we report [`DisjunctVerdict::Sat`] (the sound direction — "we could not
/// refute it"), which can only make us *fail* to discharge, never falsely discharge.
fn analyze_disjunct(conj: &[Literal]) -> DisjunctVerdict {
    // Opaque atoms: collect their asserted polarities. A literal `p` and its
    // negation `¬p` both present is an immediate contradiction.
    let mut opaque_pos: Vec<&Atom> = Vec::new();
    let mut opaque_neg: Vec<&Atom> = Vec::new();

    // Linear constraints accumulated as `expr ≤ 0` (the conjunctive part).
    let mut constraints: Vec<LinConstraint> = Vec::new();

    // Disequalities `lhs ≠ rhs`. Each is a *disjunction* `lhs < rhs ∨ lhs > rhs`, so
    // it cannot join the conjunctive `constraints` list directly. We branch over them
    // below: the conjunction is UNSAT iff it is UNSAT under *every* choice of side.
    let mut disequalities: Vec<Disequality> = Vec::new();

    // The equality theory over *opaque* (non-linear) `==`/`!=` operands. Asserted
    // equalities are unioned immediately; asserted disequalities are collected and
    // checked against the closure after every union has been processed.
    let mut eq = EqClosure::new();
    let mut opaque_disequalities: Vec<(&rv_core::Term, &rv_core::Term)> = Vec::new();
    // Every `(l, r)` we assert as an equality into the closure. Recorded so an equality
    // clash certificate can carry the exact chain the checker must replay.
    let mut asserted_eqs: Vec<(rv_core::Term, rv_core::Term)> = Vec::new();

    for lit in conj {
        match &lit.atom {
            Atom::Cmp { op, lhs, rhs } => {
                // Share every *positive* equality with the congruence closure, even
                // when it is also linear (`a == b`). This is the equality half of
                // theory combination: a linearly-stated `a == b` must still force
                // `f(a) == f(b)` by congruence. Sound — it only asserts an equality
                // that genuinely holds in this disjunct.
                if matches!(linear::effective_cmp(*op, lit.negated), Some(rv_core::BinOp::Eq)) {
                    eq.assert_eq(lhs, rhs);
                    asserted_eqs.push((lhs.clone(), rhs.clone()));
                }
                // First, is this (possibly negated) comparison a *linear* disequality?
                // Those must be split rather than turned into `≤ 0` constraints.
                if let Some(diseq) = linear::cmp_to_disequality(*op, lhs, rhs, lit.negated) {
                    disequalities.push(diseq);
                    continue;
                }
                // Otherwise turn it into the equivalent `≤ 0` constraint set.
                match linear::cmp_to_constraints(*op, lhs, rhs, lit.negated) {
                    Some(mut cs) => constraints.append(&mut cs),
                    // Not linear. If it is an `==`/`!=` over opaque terms, route it to
                    // the equality closure; otherwise keep it as a bare opaque atom.
                    None => match linear::effective_cmp(*op, lit.negated) {
                        Some(rv_core::BinOp::Eq) => eq.assert_eq(lhs, rhs),
                        Some(rv_core::BinOp::Ne) => {
                            // Intern both sides so the congruence closure can relate
                            // them (the later `equal` check is lookup-only).
                            eq.see(lhs);
                            eq.see(rhs);
                            opaque_disequalities.push((lhs, rhs));
                        }
                        _ => push_opaque(
                            &mut opaque_pos,
                            &mut opaque_neg,
                            &lit.atom,
                            lit.negated,
                        ),
                    },
                }
            }
            Atom::Opaque(_) => {
                push_opaque(&mut opaque_pos, &mut opaque_neg, &lit.atom, lit.negated)
            }
        }
    }

    // Opaque contradiction `p ∧ ¬p`?  (Syntactic identity is sufficient and sound.)
    for p in &opaque_pos {
        if opaque_neg.contains(p) {
            return DisjunctVerdict::Unsat(DisjunctCert::OpaqueClash { atom: (*p).clone() });
        }
    }

    // Saturate the congruence closure over uninterpreted applications, so that
    // `a == b` forces `f(a) == f(b)` before we test disequalities.
    eq.close();

    // Equality contradiction: an asserted opaque `l != r` whose sides are forced equal
    // by the congruence closure. (Reflexive `l != l` is caught too, since `l` is in
    // the same class as itself once seen — we `id`-intern both sides via `equal`'s
    // lookup; if a side was never seen it cannot be forced equal, so no false UNSAT.)
    for (l, r) in &opaque_disequalities {
        if eq.equal(l, r) {
            return DisjunctVerdict::Unsat(DisjunctCert::EqualityClash {
                asserted_eqs,
                diseq: ((*l).clone(), (*r).clone()),
            });
        }
    }

    // Branch over the disequalities' two sides each (a small local DNF), requiring
    // every combination to be linearly UNSAT. With no disequalities this is just the
    // single Fourier–Motzkin call on `constraints`. We collect a Farkas certificate per
    // branch (in the fixed enumeration order the checker replays).
    //
    // Note: opaque atoms with consistent polarities are freely satisfiable, so once
    // the checks above have passed they can never *help* prove UNSAT — the linear
    // verdict decides the rest.
    let mut branches = Vec::new();
    if collect_branch_farkas(&constraints, &disequalities, &mut branches) {
        DisjunctVerdict::Unsat(DisjunctCert::LinearRefutation { branches })
    } else {
        DisjunctVerdict::Sat { constraints, disequalities }
    }
}

/// Recursively branch over disequalities (`a ≠ b` ⇒ try `a < b`, then `a > b`),
/// requiring the linear part to be UNSAT under **every** branch, and pushing a Farkas
/// certificate for each refuted branch onto `out` in traversal order. Returns `true`
/// iff every branch was refuted (so `out` then holds one certificate per branch, in the
/// same order [`certificate`]'s checker re-enumerates them). On any non-refuted branch
/// it returns `false` and the caller discards `out`.
fn collect_branch_farkas(
    constraints: &[LinConstraint],
    disequalities: &[linear::Disequality],
    out: &mut Vec<FarkasCert>,
) -> bool {
    match disequalities.split_first() {
        // Base case: no disequalities left — refute the pure conjunction with Farkas.
        None => match linear::fourier_motzkin_farkas(constraints) {
            Some(multipliers) => {
                out.push(FarkasCert { multipliers });
                true
            }
            None => false,
        },
        // Inductive case: the disequality must hold via its `<` side OR its `>` side.
        // The conjunction is UNSAT iff it is UNSAT under *both*. We recurse into each
        // side in order; the checker enumerates the identical order.
        Some((d, rest)) => {
            let sides = d.sides();
            if sides.len() != 2 {
                return false; // an overflow dropped a side; cannot certify soundly.
            }
            for side in sides {
                let mut with_side = constraints.to_vec();
                with_side.push(side);
                if !collect_branch_farkas(&with_side, rest, out) {
                    return false;
                }
            }
            true
        }
    }
}

/// Record an opaque literal's polarity into the positive/negative buckets.
fn push_opaque<'a>(
    pos: &mut Vec<&'a Atom>,
    neg: &mut Vec<&'a Atom>,
    atom: &'a Atom,
    negated: bool,
) {
    if negated {
        neg.push(atom);
    } else {
        pos.push(atom);
    }
}

#[cfg(test)]
mod tests;
