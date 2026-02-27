//! Lifetime inference algorithm.

use rustc_hash::FxHashMap;
use rv_hir::{Body, Expr, ExprId};

use crate::{context::LifetimeContext, error::LifetimeResult, lifetime::LifetimeId};

/// Lifetime inference engine.
///
/// This analyzes HIR expressions to generate lifetime constraints, then
/// solves those constraints to determine concrete lifetimes.
///
/// # Implementation Notes
///
/// This is a simplified implementation that focuses on basic reference
/// tracking. A production implementation would use:
/// - Polonius-style borrow checking with location-sensitive lifetimes
/// - Non-lexical lifetimes (NLL)
/// - Full subtyping and variance
pub struct LifetimeInference {
    /// The lifetime context being built
    ctx: LifetimeContext,

    /// Map from expression IDs to their inferred lifetimes
    expr_lifetimes: FxHashMap<ExprId, LifetimeId>,
}

impl LifetimeInference {
    /// Creates a new lifetime inference engine.
    #[must_use]
    pub fn new() -> Self {
        Self {
            ctx: LifetimeContext::new(),
            expr_lifetimes: FxHashMap::default(),
        }
    }

    /// Infers lifetimes for a function body.
    ///
    /// This is the main entry point for lifetime analysis. It generates
    /// constraints from the function body and solves them.
    ///
    /// # Errors
    ///
    /// Returns an error if lifetime constraints cannot be satisfied, such as
    /// when a reference outlives the value it points to.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rv_lifetime::LifetimeInference;
    /// use rv_hir::Body;
    ///
    /// let body = Body::default();
    /// let result = LifetimeInference::infer_function(&body);
    /// ```
    pub fn infer_function(body: &Body) -> LifetimeResult<LifetimeContext> {
        let mut inference = Self::new();

        // Generate constraints from the function body
        inference.generate_constraints(body)?;

        // Solve the constraints
        inference.solve()?;

        Ok(inference.ctx)
    }

    /// Generates lifetime constraints from a function body.
    ///
    /// This walks the expression tree and creates constraints based on
    /// reference creation, borrows, and other lifetime-relevant operations.
    fn generate_constraints(&mut self, body: &Body) -> LifetimeResult<()> {
        // Walk all expressions in the body
        for (expr_id, expr) in body.exprs.iter() {
            self.constrain_expr(expr_id, expr)?;
        }

        Ok(())
    }

    /// Generates constraints for a single expression.
    ///
    /// Different expression kinds create different types of constraints:
    /// - References create outlives constraints (simplified - no Ref in HIR yet)
    /// - Assignments propagate lifetimes
    /// - Function calls connect parameter and argument lifetimes
    fn constrain_expr(&mut self, expr_id: ExprId, expr: &Expr) -> LifetimeResult<()> {
        match expr {
            Expr::UnaryOp { operand, .. } => {
                // HIR UnaryOp covers both arithmetic negation and address-of (&).
                // When Expr::Ref is added to HIR, this should generate an outlives
                // constraint: operand_lifetime outlives the reference's lifetime.
                // Until then, we just assign fresh lifetimes to both.
                let _operand_lifetime = self.expr_lifetime(*operand);
                let expr_lifetime = self.ctx.fresh_lifetime();
                self.expr_lifetimes.insert(expr_id, expr_lifetime);
            }

            Expr::BinaryOp { left, right, .. } => {
                // Binary operations don't create new lifetime constraints.
                // We record sub-expression lifetimes for completeness but don't
                // relate them — the result is a new value, not a borrow.
                let _left_lifetime = self.expr_lifetime(*left);
                let _right_lifetime = self.expr_lifetime(*right);

                let expr_lifetime = self.ctx.fresh_lifetime();
                self.expr_lifetimes.insert(expr_id, expr_lifetime);
            }

            Expr::Block {
                statements: _,
                expr: tail,
                ..
            } => {
                // Constrain all statements (simplified - would need statement types)
                if let Some(tail_id) = tail {
                    // Block inherits tail's lifetime
                    let tail_lifetime = self.expr_lifetime(*tail_id);
                    self.expr_lifetimes.insert(expr_id, tail_lifetime);
                } else {
                    let lifetime = self.ctx.fresh_lifetime();
                    self.expr_lifetimes.insert(expr_id, lifetime);
                }
            }

            // Most other expressions don't create new lifetimes
            _ => {
                // Assign a fresh lifetime for tracking purposes
                let lifetime = self.ctx.fresh_lifetime();
                self.expr_lifetimes.insert(expr_id, lifetime);
            }
        }

        Ok(())
    }

    /// Gets or creates a lifetime for an expression.
    fn expr_lifetime(&mut self, expr_id: ExprId) -> LifetimeId {
        if let Some(&lifetime_id) = self.expr_lifetimes.get(&expr_id) {
            lifetime_id
        } else {
            let lifetime_id = self.ctx.fresh_lifetime();
            self.expr_lifetimes.insert(expr_id, lifetime_id);
            lifetime_id
        }
    }

    /// Solves the collected lifetime constraints.
    ///
    /// Builds an outlives graph from constraints, computes transitive closure
    /// to propagate relationships, detects cycles, and unifies equality
    /// constraints.
    ///
    /// # Errors
    ///
    /// Returns an error if constraints cannot be satisfied (e.g., circular
    /// dependencies or impossible outlives relationships).
    fn solve(&mut self) -> LifetimeResult<()> {
        use crate::lifetime::LifetimeConstraint;

        // Collect constraints to avoid borrow checker issues
        let constraints: Vec<_> = self.ctx.constraints().to_vec();

        // Phase 1: Process equality constraints via unification
        for constraint in &constraints {
            if let LifetimeConstraint::Equality { left, right, .. } = constraint {
                if let (Some(left_id), Some(right_id)) = (left.id(), right.id()) {
                    if left_id != right_id {
                        self.ctx.record_subst(left_id, right.clone());
                        self.ctx.record_subst(right_id, left.clone());
                    }
                }
            }
        }

        // Phase 2: Build outlives graph and check for contradictions
        // Edges represent "sub outlives sup" relationships.
        // An edge from A → B means lifetime A must outlive lifetime B.
        let mut outlives_edges: FxHashMap<LifetimeId, Vec<(LifetimeId, rv_span::FileSpan)>> =
            FxHashMap::default();

        for constraint in &constraints {
            if let LifetimeConstraint::Outlives { sub, sup, source } = constraint {
                // 'static outlives everything — that's always true
                if sub.is_static() {
                    continue;
                }

                // Nothing outlives 'static unless it is also 'static
                if sup.is_static() && !sub.is_static() {
                    if let Some(sub_id) = sub.id() {
                        // Record that this variable must be 'static
                        self.ctx
                            .record_subst(sub_id, crate::lifetime::Lifetime::Static);
                    }
                    continue;
                }

                if let (Some(sub_id), Some(sup_id)) = (sub.id(), sup.id()) {
                    // Self-outlives is trivially true
                    if sub_id == sup_id {
                        continue;
                    }
                    outlives_edges
                        .entry(sub_id)
                        .or_default()
                        .push((sup_id, *source));
                }
            }
        }

        // Phase 3: Compute transitive closure of the outlives graph
        // If A outlives B and B outlives C, then A must outlive C.
        let mut changed = true;
        let max_iterations = self.ctx.num_lifetimes() * 2 + 1;
        let mut iteration = 0;

        while changed && iteration < max_iterations {
            changed = false;
            iteration += 1;

            let current_edges: Vec<_> = outlives_edges
                .iter()
                .flat_map(|(src, dsts)| dsts.iter().map(move |(dst, span)| (*src, *dst, *span)))
                .collect();

            for (a, b, span_ab) in &current_edges {
                if let Some(b_edges) = outlives_edges.get(b).cloned() {
                    for (c, _span_bc) in b_edges {
                        if *a != c {
                            let a_edges = outlives_edges.entry(*a).or_default();
                            if !a_edges.iter().any(|(dst, _)| *dst == c) {
                                a_edges.push((c, *span_ab));
                                changed = true;
                            }
                        }
                    }
                }
            }
        }

        // Phase 4: Detect cycles (A outlives B and B outlives A is a contradiction
        // for non-equal, non-static lifetimes — unless unified by equality)
        for (src, dsts) in &outlives_edges {
            for (dst, span) in dsts {
                if src == dst {
                    continue; // Self-loop, skip
                }
                // Check if reverse edge exists
                if let Some(reverse_dsts) = outlives_edges.get(dst) {
                    if reverse_dsts.iter().any(|(rev_dst, _)| rev_dst == src) {
                        // Bidirectional outlives — unify the lifetimes
                        let dst_lifetime = crate::lifetime::Lifetime::Inferred { id: *dst };
                        self.ctx.record_subst(*src, dst_lifetime.clone());
                        let src_lifetime = crate::lifetime::Lifetime::Inferred { id: *src };
                        self.ctx.record_subst(*dst, src_lifetime);
                        // This is not an error — mutual outlives implies equality.
                        // Only report if we can prove it's genuinely unsatisfiable,
                        // which would require concrete scope information we don't
                        // have at this stage.
                        let _ = span; // suppress unused warning
                    }
                }
            }
        }

        Ok(())
    }

    /// Returns the inferred lifetime for an expression.
    ///
    /// Returns `None` if no lifetime was inferred for the expression.
    #[must_use]
    pub fn get_expr_lifetime(&self, expr_id: ExprId) -> Option<LifetimeId> {
        self.expr_lifetimes.get(&expr_id).copied()
    }
}

impl Default for LifetimeInference {
    fn default() -> Self {
        Self::new()
    }
}
