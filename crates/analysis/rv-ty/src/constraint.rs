//! Type constraint system
//!
//! This module defines the constraint-based type inference system that enables
//! module-level type inference and proper generic type instantiation.

use crate::ty::TyId;
use rv_hir::{FunctionId, TraitId};
use rv_span::{FileId, Span};

/// A type constraint generated during type inference
#[derive(Debug, Clone)]
pub enum Constraint {
    /// Two types must be equal
    Equality {
        /// Left type
        left: TyId,
        /// Right type
        right: TyId,
        /// Source of this constraint
        source: ConstraintSource,
    },
    /// A type must satisfy a trait bound
    TraitBound {
        /// Type that must implement the trait
        ty: TyId,
        /// Trait that must be implemented
        trait_id: TraitId,
        /// Source of this constraint
        source: ConstraintSource,
    },
    /// A generic parameter must be instantiated to a concrete type
    GenericInstantiation {
        /// Function being instantiated
        function: FunctionId,
        /// Index of the generic parameter
        param_index: usize,
        /// Concrete type for this parameter
        ty: TyId,
        /// Source of this constraint
        source: ConstraintSource,
    },
}

/// Source location and reason for a constraint
#[derive(Debug, Clone)]
pub struct ConstraintSource {
    /// File where constraint originated
    pub file_id: FileId,
    /// Span in the source file
    pub span: Span,
    /// Human-readable reason for the constraint
    pub reason: String,
}

impl ConstraintSource {
    /// Create a new constraint source
    #[must_use]
    pub fn new(file_id: FileId, span: Span, reason: String) -> Self {
        Self {
            file_id,
            span,
            reason,
        }
    }

    /// Create a constraint source for a function argument
    #[must_use]
    pub fn function_argument(file_id: FileId, span: Span, arg_index: usize) -> Self {
        Self {
            file_id,
            span,
            reason: format!("function argument {arg_index}"),
        }
    }

    /// Create a constraint source for a return type
    #[must_use]
    pub fn return_type(file_id: FileId, span: Span) -> Self {
        Self {
            file_id,
            span,
            reason: "return type".to_string(),
        }
    }

    /// Create a constraint source for a let binding
    #[must_use]
    pub fn let_binding(file_id: FileId, span: Span) -> Self {
        Self {
            file_id,
            span,
            reason: "let binding".to_string(),
        }
    }

    /// Create a constraint source for a binary operation
    #[must_use]
    pub fn binary_op(file_id: FileId, span: Span, op: &str) -> Self {
        Self {
            file_id,
            span,
            reason: format!("binary operation '{op}'"),
        }
    }

    /// Create a constraint source for a generic instantiation
    #[must_use]
    pub fn generic_instantiation(file_id: FileId, span: Span, param_name: &str) -> Self {
        Self {
            file_id,
            span,
            reason: format!("generic parameter '{param_name}'"),
        }
    }
}

/// Collection of type constraints
#[derive(Debug, Clone)]
pub struct Constraints {
    /// All constraints
    constraints: Vec<Constraint>,
}

impl Constraints {
    /// Create a new empty constraint set
    #[must_use]
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
        }
    }

    /// Add an equality constraint
    pub fn add_equality(&mut self, left: TyId, right: TyId, source: ConstraintSource) {
        self.constraints.push(Constraint::Equality {
            left,
            right,
            source,
        });
    }

    /// Add a trait bound constraint
    pub fn add_trait_bound(&mut self, ty: TyId, trait_id: TraitId, source: ConstraintSource) {
        self.constraints.push(Constraint::TraitBound {
            ty,
            trait_id,
            source,
        });
    }

    /// Add a generic instantiation constraint
    pub fn add_generic_instantiation(
        &mut self,
        function: FunctionId,
        param_index: usize,
        ty: TyId,
        source: ConstraintSource,
    ) {
        self.constraints.push(Constraint::GenericInstantiation {
            function,
            param_index,
            ty,
            source,
        });
    }

    /// Get all constraints
    #[must_use]
    pub fn all(&self) -> &[Constraint] {
        &self.constraints
    }

    /// Get a mutable reference to all constraints
    pub fn all_mut(&mut self) -> &mut Vec<Constraint> {
        &mut self.constraints
    }

    /// Get the number of constraints
    #[must_use]
    pub fn len(&self) -> usize {
        self.constraints.len()
    }

    /// Check if there are no constraints
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }

    /// Clear all constraints
    pub fn clear(&mut self) {
        self.constraints.clear();
    }

    /// Extend with constraints from another set
    pub fn extend(&mut self, other: Constraints) {
        self.constraints.extend(other.constraints);
    }

    /// Filter constraints by predicate
    pub fn filter<F>(&mut self, mut predicate: F)
    where
        F: FnMut(&Constraint) -> bool,
    {
        self.constraints.retain(|c| predicate(c));
    }

    /// Iterate over constraints
    pub fn iter(&self) -> impl Iterator<Item = &Constraint> {
        self.constraints.iter()
    }
}

impl Default for Constraints {
    fn default() -> Self {
        Self::new()
    }
}

impl IntoIterator for Constraints {
    type Item = Constraint;
    type IntoIter = std::vec::IntoIter<Constraint>;

    fn into_iter(self) -> Self::IntoIter {
        self.constraints.into_iter()
    }
}

impl<'a> IntoIterator for &'a Constraints {
    type Item = &'a Constraint;
    type IntoIter = std::slice::Iter<'a, Constraint>;

    fn into_iter(self) -> Self::IntoIter {
        self.constraints.iter()
    }
}

impl FromIterator<Constraint> for Constraints {
    fn from_iter<T: IntoIterator<Item = Constraint>>(iter: T) -> Self {
        Self {
            constraints: iter.into_iter().collect(),
        }
    }
}
