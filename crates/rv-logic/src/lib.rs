//! The logic layer: the obligation type, a *registry* of pluggable solvers (no
//! Pure/Spatial/Atomic enum — routing is data), and the ownership trait surface
//! (resource algebra + usage semiring) that disciplines plug into.
use rv_core::Prop;

pub mod lia;
pub use lia::{
    Atom, DisjunctCert, Disequality, EqClosure, FarkasCert, LiaCertificate, LinConstraint, LinExpr,
    Literal, OpaqueAtom, Rat,
};

/// A verification obligation: prove `goal` under hypotheses `ctx`. Both are `Prop`.
#[derive(Clone, Debug)]
pub struct Obligation {
    pub ctx: Prop,
    pub goal: Prop,
    /// Human-readable source of the obligation (for diagnostics).
    pub origin: String,
}
impl Obligation {
    pub fn new(ctx: Prop, goal: Prop, origin: impl Into<String>) -> Self {
        Self { ctx, goal, origin: origin.into() }
    }
}

/// Evidence that a goal holds.
///
/// [`Certificate::Replay`] is checked directly against the original obligation;
/// the producer of that certificate is therefore untrusted. [`Certificate::Lia`]
/// carries a full, independently-checkable linear-arithmetic + congruence unsat
/// certificate together with the DNF disjuncts it refutes, so its producer
/// (`rv-solve`'s search) is *also* untrusted — anyone holding the `Certificate` can
/// re-run [`lia::LiaCertificate::check`] via [`Certificate::check`]. `Trusted` remains
/// a temporary escape hatch for decision procedures that have not yet learned to emit
/// a replayable proof object.
#[derive(Clone, Debug)]
pub enum Certificate {
    Replay(ReplayCertificate),
    /// A checkable linear-arithmetic / congruence refutation of `ctx ∧ ¬goal`.
    ///
    /// Holds both the structured [`LiaCertificate`] and the exact DNF `disjuncts`
    /// (the literal lists) it was built against. [`Certificate::check`] re-verifies the
    /// pair by pure arithmetic and union–find rebuild — calling nothing in the solver's
    /// search. A tampered certificate (wrong Farkas coefficient, fabricated equality,
    /// missing disjunct) fails to validate and the obligation is treated as unproved.
    Lia { certificate: LiaCertificate, disjuncts: Vec<Vec<Literal>> },
    Trusted { by: &'static str },
}

/// A tiny, independently replayable fragment of propositional evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReplayCertificate {
    GoalTrue,
    ContextContainsFalse,
    ContextContainsGoal,
}

impl Certificate {
    pub fn trusted(by: &'static str) -> Self {
        Certificate::Trusted { by }
    }

    /// Validate a replay certificate against its source obligation. Trusted
    /// certificates deliberately return true until their solver has a proof
    /// format; callers can inspect [`Self::is_replayable`] for trust reporting.
    pub fn check(&self, ob: &Obligation) -> bool {
        match self {
            Certificate::Replay(ReplayCertificate::GoalTrue) => matches!(ob.goal, Prop::True),
            Certificate::Replay(ReplayCertificate::ContextContainsFalse) => {
                context_contains_false(&ob.ctx)
            }
            Certificate::Replay(ReplayCertificate::ContextContainsGoal) => {
                conjuncts_contain(&ob.ctx, &ob.goal)
            }
            Certificate::Lia { certificate, disjuncts } => {
                // Independently re-derive the DNF of `ctx ∧ ¬goal` for *this* obligation
                // and require it to match the disjuncts the certificate ships with. This
                // binds the certificate to the obligation: a producer cannot smuggle in a
                // proof of some *other* (valid) formula. Then re-check the certificate
                // against those disjuncts by pure arithmetic / union–find — calling
                // nothing in the solver's search.
                match lia::disjuncts_of(&ob.ctx, &ob.goal, lia::MAX_DISJUNCTS) {
                    Some(derived) if &derived == disjuncts => certificate.check(disjuncts),
                    _ => false,
                }
            }
            Certificate::Trusted { .. } => true,
        }
    }

    /// A certificate is *replayable* (its producer untrusted) when the consumer can
    /// re-verify it independently — the structural [`Certificate::Replay`] fragments and
    /// the arithmetic [`Certificate::Lia`] certificate both qualify. Only
    /// [`Certificate::Trusted`] leaves its producer in the trust base.
    pub fn is_replayable(&self) -> bool {
        matches!(self, Certificate::Replay(_) | Certificate::Lia { .. })
    }
}

fn context_contains_false(p: &Prop) -> bool {
    match p {
        Prop::False => true,
        Prop::And(a, b) => context_contains_false(a) || context_contains_false(b),
        _ => false,
    }
}

fn conjuncts_contain(ctx: &Prop, goal: &Prop) -> bool {
    match ctx {
        Prop::And(a, b) => conjuncts_contain(a, goal) || conjuncts_contain(b, goal),
        other => other == goal,
    }
}

/// Where a fact's truth comes from — proved vs trusted.
#[derive(Clone, Debug)]
pub enum Provenance {
    Proved(Certificate),
    Assumed(String),
    TrustedBase(&'static str),
}

/// The result of attempting an obligation.
#[derive(Clone, Debug)]
pub enum Outcome {
    Discharged(Certificate),
    /// Failed, optionally with a counterexample description.
    Failed(Option<String>),
}
impl Outcome {
    pub fn is_discharged(&self) -> bool {
        matches!(self, Outcome::Discharged(_))
    }

    /// A solver result is usable only when any attached replay certificate checks
    /// against this exact obligation.
    pub fn checks(&self, ob: &Obligation) -> bool {
        matches!(self, Outcome::Discharged(cert) if cert.check(ob))
    }
}

/// A discharge strategy. SMT, separation-logic tactics, etc. are all `Solver`s;
/// the obligation type knows about none of them.
pub trait Solver {
    fn name(&self) -> &'static str;
    fn try_solve(&self, ob: &Obligation) -> Outcome;
}

/// Try each registered solver until one discharges the goal.
#[derive(Default)]
pub struct SolverRegistry {
    solvers: Vec<Box<dyn Solver>>,
}
impl SolverRegistry {
    pub fn new() -> Self {
        Self { solvers: Vec::new() }
    }
    pub fn register(&mut self, solver: Box<dyn Solver>) {
        self.solvers.push(solver);
    }
    pub fn discharge(&self, ob: &Obligation) -> Outcome {
        let mut last = Outcome::Failed(None);
        for s in &self.solvers {
            match s.try_solve(ob) {
                Outcome::Discharged(c) => return Outcome::Discharged(c),
                other => last = other,
            }
        }
        last
    }
}

/// A resource algebra (partial commutative monoid + validity): the pluggable
/// ownership substrate. Borrow/GC/RC supply instances; the IR core names none.
pub trait ResourceAlgebra {
    type R: Clone;
    fn unit() -> Self::R;
    fn compose(a: &Self::R, b: &Self::R) -> Option<Self::R>;
    fn valid(a: &Self::R) -> bool;
}

/// A usage semiring (QTT grades): linear / affine / unrestricted / security levels.
pub trait Grades {
    type G: Clone + PartialEq;
    fn zero() -> Self::G;
    fn one() -> Self::G;
    fn add(a: &Self::G, b: &Self::G) -> Self::G;
    fn mul(a: &Self::G, b: &Self::G) -> Self::G;
    fn leq(a: &Self::G, b: &Self::G) -> bool;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replay_certificates_are_bound_to_their_obligation() {
        let true_goal = Obligation::new(Prop::False, Prop::True, "test");
        let cert = Certificate::Replay(ReplayCertificate::GoalTrue);
        assert!(cert.check(&true_goal));

        let non_true_goal = Obligation::new(Prop::True, Prop::False, "test");
        assert!(!cert.check(&non_true_goal));
    }
}
