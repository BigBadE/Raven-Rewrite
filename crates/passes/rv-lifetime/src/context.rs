//! Lifetime inference context.

use rustc_hash::FxHashMap;

use crate::lifetime::{Lifetime, LifetimeConstraint, LifetimeId};

/// Context for lifetime inference.
///
/// This tracks all lifetime variables, constraints between them, and the
/// final solutions after constraint solving.
#[derive(Debug)]
pub struct LifetimeContext {
    /// All lifetime variables created during inference
    lifetime_vars: Vec<Lifetime>,

    /// Constraints between lifetimes that must be satisfied
    constraints: Vec<LifetimeConstraint>,

    /// Resolved substitutions after constraint solving
    subst: FxHashMap<LifetimeId, Lifetime>,

    /// Next lifetime ID to allocate
    next_id: u32,
}

impl LifetimeContext {
    /// Creates a new empty lifetime context.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rv_lifetime::LifetimeContext;
    ///
    /// let ctx = LifetimeContext::new();
    /// ```
    #[must_use]
    pub fn new() -> Self {
        Self {
            lifetime_vars: Vec::new(),
            constraints: Vec::new(),
            subst: FxHashMap::default(),
            next_id: 0,
        }
    }

    /// Creates a fresh lifetime inference variable.
    ///
    /// Returns a unique lifetime ID that can be used to create lifetime
    /// variables and constraints.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rv_lifetime::LifetimeContext;
    ///
    /// let mut ctx = LifetimeContext::new();
    /// let lifetime_id = ctx.fresh_lifetime();
    /// ```
    pub fn fresh_lifetime(&mut self) -> LifetimeId {
        let id = LifetimeId(self.next_id);
        self.next_id += 1;
        self.lifetime_vars.push(Lifetime::Inferred { id });
        id
    }

    /// Adds a constraint that must be satisfied.
    ///
    /// Constraints are collected during inference and solved later.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rv_lifetime::{LifetimeContext, Lifetime, LifetimeId};
    /// use rv_lifetime::lifetime::LifetimeConstraint;
    /// use rv_span::{FileId, FileSpan, Span};
    ///
    /// let mut ctx = LifetimeContext::new();
    /// let id1 = ctx.fresh_lifetime();
    /// let id2 = ctx.fresh_lifetime();
    /// let span = FileSpan::new(FileId(0), Span::new(0, 0));
    /// let constraint = LifetimeConstraint::outlives(
    ///     Lifetime::inferred(id1),
    ///     Lifetime::inferred(id2),
    ///     span,
    /// );
    /// ctx.add_constraint(constraint);
    /// ```
    pub fn add_constraint(&mut self, constraint: LifetimeConstraint) {
        self.constraints.push(constraint);
    }

    /// Adds an outlives constraint: `sub` outlives `sup`.
    ///
    /// This is a convenience method for adding outlives constraints.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rv_lifetime::{LifetimeContext, Lifetime};
    /// use rv_span::{FileId, FileSpan, Span};
    ///
    /// let mut ctx = LifetimeContext::new();
    /// let span = FileSpan::new(FileId(0), Span::new(0, 0));
    /// ctx.add_outlives(Lifetime::Static, Lifetime::Error, span);
    /// ```
    pub fn add_outlives(&mut self, sub: Lifetime, sup: Lifetime, source: rv_span::FileSpan) {
        self.add_constraint(LifetimeConstraint::Outlives { sub, sup, source });
    }

    /// Adds an equality constraint: `left` equals `right`.
    ///
    /// This is a convenience method for adding equality constraints.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rv_lifetime::{LifetimeContext, Lifetime};
    /// use rv_span::{FileId, FileSpan, Span};
    ///
    /// let mut ctx = LifetimeContext::new();
    /// let span = FileSpan::new(FileId(0), Span::new(0, 0));
    /// ctx.add_equality(Lifetime::Static, Lifetime::Static, span);
    /// ```
    pub fn add_equality(&mut self, left: Lifetime, right: Lifetime, source: rv_span::FileSpan) {
        self.add_constraint(LifetimeConstraint::Equality {
            left,
            right,
            source,
        });
    }

    /// Returns all constraints collected so far.
    #[must_use]
    pub fn constraints(&self) -> &[LifetimeConstraint] {
        &self.constraints
    }

    /// Returns all lifetime variables created.
    #[must_use]
    pub fn lifetime_vars(&self) -> &[Lifetime] {
        &self.lifetime_vars
    }

    /// Looks up the substitution for a lifetime ID.
    ///
    /// Returns `None` if the lifetime hasn't been solved yet.
    #[must_use]
    pub fn lookup_subst(&self, id: LifetimeId) -> Option<&Lifetime> {
        self.subst.get(&id)
    }

    /// Records a substitution for a lifetime ID.
    ///
    /// This is used during constraint solving to record the solution.
    pub fn record_subst(&mut self, id: LifetimeId, lifetime: Lifetime) {
        self.subst.insert(id, lifetime);
    }

    /// Returns the number of lifetime variables created.
    #[must_use]
    pub fn num_lifetimes(&self) -> usize {
        self.lifetime_vars.len()
    }

    /// Returns the number of constraints.
    #[must_use]
    pub fn num_constraints(&self) -> usize {
        self.constraints.len()
    }
}

impl Default for LifetimeContext {
    fn default() -> Self {
        Self::new()
    }
}
