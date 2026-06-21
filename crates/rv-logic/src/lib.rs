//! The logic layer: the obligation type, a *registry* of pluggable solvers (no
//! Pure/Spatial/Atomic enum — routing is data), and the ownership trait surface
//! (resource algebra + usage semiring) that disciplines plug into.
use rv_core::Prop;

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

/// Evidence that a goal holds. (Designed to later carry a kernel-checkable proof
/// term; for now its presence means a trusted solver accepted the goal.)
#[derive(Clone, Debug)]
pub struct Certificate {
    pub by: &'static str,
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
