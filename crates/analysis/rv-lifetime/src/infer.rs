//! Lifetime inference algorithm.

use rustc_hash::FxHashMap;
use rv_hir::{Body, Expr, ExprId};

use crate::{
    context::LifetimeContext,
    error::{LifetimeError, LifetimeResult},
    lifetime::LifetimeId,
};

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
                // For now, we don't distinguish reference operations in HIR
                // This is a simplified placeholder for when Ref operations are added
                let _operand_lifetime = self.expr_lifetime(*operand);
                let expr_lifetime = self.ctx.fresh_lifetime();
                self.expr_lifetimes.insert(expr_id, expr_lifetime);
            }

            Expr::BinaryOp { left, right, .. } => {
                // Binary operations typically don't create new lifetimes
                // The result lifetime is based on the operands
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
    /// This implements a simplified constraint solver. A production
    /// implementation would use a proper outlives graph with cycle detection
    /// and transitive closure.
    ///
    /// # Errors
    ///
    /// Returns an error if constraints cannot be satisfied (e.g., circular
    /// dependencies or impossible outlives relationships).
    fn solve(&mut self) -> LifetimeResult<()> {
        // Simplified constraint solving
        // A full implementation would:
        // 1. Build an outlives graph
        // 2. Check for cycles
        // 3. Compute transitive closure
        // 4. Verify all constraints are satisfiable

        // Collect constraints to avoid borrow checker issues
        let constraints: Vec<_> = self.ctx.constraints().to_vec();

        // For now, we just check for obvious contradictions
        for constraint in &constraints {
            match constraint {
                crate::lifetime::LifetimeConstraint::Outlives { sub, sup, source: _ } => {
                    // Check for trivially unsatisfiable constraints
                    if sub == sup && !sub.is_static() {
                        return Err(LifetimeError::UnsatisfiableConstraint {
                            constraint: format!("{sub:?}: {sup:?}"),
                            span: constraint.source(),
                        });
                    }
                }
                crate::lifetime::LifetimeConstraint::Equality {
                    left,
                    right,
                    source: _,
                } => {
                    // Equality constraints are always satisfiable by unification
                    if let (Some(left_id), Some(right_id)) = (left.id(), right.id()) {
                        if left_id != right_id {
                            self.ctx.record_subst(left_id, right.clone());
                            self.ctx.record_subst(right_id, left.clone());
                        }
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
