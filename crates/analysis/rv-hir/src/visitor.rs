//! HIR visitor infrastructure for traversing HIR nodes

use crate::{Body, Expr, ExprId, Pattern, PatternId, Stmt, StmtId};

/// Visitor trait for HIR expressions
pub trait ExprVisitor {
    /// Output type produced by visiting an expression
    type Output;

    /// Visit an expression by ID
    fn visit_expr(&mut self, expr_id: ExprId, body: &Body) -> Self::Output {
        let expr = &body.exprs[expr_id];
        self.visit_expr_kind(expr, expr_id, body)
    }

    /// Visit an expression kind (can be overridden)
    #[allow(clippy::too_many_lines, reason = "Visitor dispatch for all expression variants")]
    fn visit_expr_kind(&mut self, expr: &Expr, expr_id: ExprId, body: &Body) -> Self::Output {
        match expr {
            Expr::Literal { .. } => self.visit_literal(expr_id, body),
            Expr::Variable { .. } => self.visit_variable(expr_id, body),
            Expr::BinaryOp { op, left, right, .. } => {
                self.visit_binary_op(*op, *left, *right, expr_id, body)
            }
            Expr::UnaryOp { op, operand, .. } => self.visit_unary_op(*op, *operand, expr_id, body),
            Expr::Call { callee, args, .. } => self.visit_call(*callee, args, expr_id, body),
            Expr::MethodCall {
                receiver,
                method,
                args,
                ..
            } => self.visit_method_call(*receiver, *method, args, expr_id, body),
            Expr::Field { base, field, .. } => {
                self.visit_field(*base, *field, expr_id, body)
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => self.visit_if(*condition, *then_branch, *else_branch, expr_id, body),
            Expr::Block {
                statements, expr, ..
            } => self.visit_block(statements, *expr, expr_id, body),
            Expr::Match { scrutinee, arms, .. } => self.visit_match(*scrutinee, arms, expr_id, body),
            Expr::StructConstruct { struct_name, fields, .. } => {
                self.visit_struct_construct(*struct_name, fields, expr_id, body)
            }
            Expr::EnumVariant {
                enum_name,
                variant,
                fields,
                ..
            } => self.visit_enum_variant(*enum_name, *variant, fields, expr_id, body),
            Expr::Closure {
                params, body: closure_body, ..
            } => self.visit_closure(params, *closure_body, expr_id, body),
        }
    }

    // Individual visit methods with default implementations that recurse

    /// Visit literal expression
    fn visit_literal(&mut self, expr_id: ExprId, body: &Body) -> Self::Output {
        self.default_output(expr_id, body)
    }

    /// Visit variable expression
    fn visit_variable(&mut self, expr_id: ExprId, body: &Body) -> Self::Output {
        self.default_output(expr_id, body)
    }

    /// Visit binary operation
    fn visit_binary_op(
        &mut self,
        _op: crate::BinaryOp,
        left: ExprId,
        right: ExprId,
        expr_id: ExprId,
        body: &Body,
    ) -> Self::Output {
        self.visit_expr(left, body);
        self.visit_expr(right, body);
        self.default_output(expr_id, body)
    }

    /// Visit unary operation
    fn visit_unary_op(
        &mut self,
        _op: crate::UnaryOp,
        operand: ExprId,
        expr_id: ExprId,
        body: &Body,
    ) -> Self::Output {
        self.visit_expr(operand, body);
        self.default_output(expr_id, body)
    }

    /// Visit function call
    fn visit_call(
        &mut self,
        callee: ExprId,
        args: &[ExprId],
        expr_id: ExprId,
        body: &Body,
    ) -> Self::Output {
        self.visit_expr(callee, body);
        for arg_id in args {
            self.visit_expr(*arg_id, body);
        }
        self.default_output(expr_id, body)
    }

    /// Visit method call
    fn visit_method_call(
        &mut self,
        receiver: ExprId,
        _method_name: rv_intern::Symbol,
        args: &[ExprId],
        expr_id: ExprId,
        body: &Body,
    ) -> Self::Output {
        self.visit_expr(receiver, body);
        for arg_id in args {
            self.visit_expr(*arg_id, body);
        }
        self.default_output(expr_id, body)
    }

    /// Visit field access
    fn visit_field(
        &mut self,
        base: ExprId,
        _field_name: rv_intern::Symbol,
        expr_id: ExprId,
        body: &Body,
    ) -> Self::Output {
        self.visit_expr(base, body);
        self.default_output(expr_id, body)
    }

    /// Visit if expression
    fn visit_if(
        &mut self,
        condition: ExprId,
        then_branch: ExprId,
        else_branch: Option<ExprId>,
        expr_id: ExprId,
        body: &Body,
    ) -> Self::Output {
        self.visit_expr(condition, body);
        self.visit_expr(then_branch, body);
        if let Some(else_id) = else_branch {
            self.visit_expr(else_id, body);
        }
        self.default_output(expr_id, body)
    }

    /// Visit block expression
    fn visit_block(
        &mut self,
        statements: &[StmtId],
        expr: Option<ExprId>,
        expr_id: ExprId,
        body: &Body,
    ) -> Self::Output {
        for stmt_id in statements {
            self.visit_stmt(*stmt_id, body);
        }
        if let Some(expr_id_inner) = expr {
            self.visit_expr(expr_id_inner, body);
        }
        self.default_output(expr_id, body)
    }

    /// Visit match expression
    fn visit_match(
        &mut self,
        scrutinee: ExprId,
        arms: &[crate::MatchArm],
        expr_id: ExprId,
        body: &Body,
    ) -> Self::Output {
        self.visit_expr(scrutinee, body);
        for arm in arms {
            self.visit_pattern(arm.pattern, body);
            self.visit_expr(arm.body, body);
        }
        self.default_output(expr_id, body)
    }

    /// Visit struct construction
    fn visit_struct_construct(
        &mut self,
        _type_name: rv_intern::Symbol,
        fields: &[(rv_intern::Symbol, ExprId)],
        expr_id: ExprId,
        body: &Body,
    ) -> Self::Output {
        for (_, field_expr) in fields {
            self.visit_expr(*field_expr, body);
        }
        self.default_output(expr_id, body)
    }

    /// Visit enum variant construction
    fn visit_enum_variant(
        &mut self,
        _enum_name: rv_intern::Symbol,
        _variant_name: rv_intern::Symbol,
        fields: &[ExprId],
        expr_id: ExprId,
        body: &Body,
    ) -> Self::Output {
        for field_expr in fields {
            self.visit_expr(*field_expr, body);
        }
        self.default_output(expr_id, body)
    }

    /// Visit closure
    fn visit_closure(
        &mut self,
        _params: &[crate::Parameter],
        closure_body: ExprId,
        expr_id: ExprId,
        body: &Body,
    ) -> Self::Output {
        self.visit_expr(closure_body, body);
        self.default_output(expr_id, body)
    }

    /// Visit statement (for blocks)
    fn visit_stmt(&mut self, stmt_id: StmtId, body: &Body) {
        let stmt = &body.stmts[stmt_id];
        match stmt {
            Stmt::Expr { expr, .. } => {
                self.visit_expr(*expr, body);
            }
            Stmt::Let { initializer, .. } => {
                if let Some(val_expr) = initializer {
                    self.visit_expr(*val_expr, body);
                }
            }
            Stmt::Return { value, .. } => {
                if let Some(val_expr) = value {
                    self.visit_expr(*val_expr, body);
                }
            }
        }
    }

    /// Visit pattern (for match arms)
    fn visit_pattern(&mut self, _pattern_id: PatternId, _body: &Body) {
        // Default: do nothing (can be overridden)
    }

    /// Default output for an expression (must be implemented)
    fn default_output(&mut self, expr_id: ExprId, body: &Body) -> Self::Output;
}

/// Visitor trait for HIR statements
pub trait StmtVisitor {
    /// Output type produced by visiting a statement
    type Output;

    /// Visit a statement by ID
    fn visit_stmt(&mut self, stmt_id: StmtId, body: &Body) -> Self::Output {
        let stmt = &body.stmts[stmt_id];
        self.visit_stmt_kind(stmt, stmt_id, body)
    }

    /// Visit a statement kind
    fn visit_stmt_kind(&mut self, stmt: &Stmt, stmt_id: StmtId, body: &Body) -> Self::Output {
        match stmt {
            Stmt::Expr { expr, .. } => self.visit_expr_stmt(*expr, stmt_id, body),
            Stmt::Let {
                pattern, ty, initializer, ..
            } => self.visit_let_stmt(*pattern, *ty, *initializer, stmt_id, body),
            Stmt::Return { value, .. } => self.visit_return_stmt(*value, stmt_id, body),
        }
    }

    /// Visit expression statement
    fn visit_expr_stmt(&mut self, _expr: ExprId, stmt_id: StmtId, body: &Body) -> Self::Output {
        self.default_output(stmt_id, body)
    }

    /// Visit let statement
    fn visit_let_stmt(
        &mut self,
        _pattern: PatternId,
        _ty: Option<crate::TypeId>,
        _initializer: Option<ExprId>,
        stmt_id: StmtId,
        body: &Body,
    ) -> Self::Output {
        self.default_output(stmt_id, body)
    }

    /// Visit return statement
    fn visit_return_stmt(&mut self, _value: Option<ExprId>, stmt_id: StmtId, body: &Body) -> Self::Output {
        self.default_output(stmt_id, body)
    }

    /// Default output for a statement (must be implemented)
    fn default_output(&mut self, stmt_id: StmtId, body: &Body) -> Self::Output;
}

/// Visitor trait for HIR patterns
pub trait PatternVisitor {
    /// Output type produced by visiting a pattern
    type Output;

    /// Visit a pattern by ID
    fn visit_pattern(&mut self, pattern_id: PatternId, body: &Body) -> Self::Output {
        let pattern = &body.patterns[pattern_id];
        self.visit_pattern_kind(pattern, pattern_id, body)
    }

    /// Visit a pattern kind
    fn visit_pattern_kind(&mut self, pattern: &Pattern, pattern_id: PatternId, body: &Body) -> Self::Output {
        match pattern {
            Pattern::Wildcard { .. } => self.visit_wildcard(pattern_id, body),
            Pattern::Literal { .. } => self.visit_literal_pattern(pattern_id, body),
            Pattern::Binding { .. } => self.visit_binding(pattern_id, body),
            Pattern::Tuple { patterns, .. } => self.visit_tuple_pattern(patterns, pattern_id, body),
            Pattern::Struct { fields, .. } => self.visit_struct_pattern(fields, pattern_id, body),
            Pattern::Enum { sub_patterns, .. } => {
                self.visit_enum_pattern(sub_patterns, pattern_id, body)
            }
            Pattern::Or { patterns, .. } => self.visit_or_pattern(patterns, pattern_id, body),
            Pattern::Range { .. } => self.visit_range_pattern(pattern_id, body),
        }
    }

    /// Visit wildcard pattern
    fn visit_wildcard(&mut self, pattern_id: PatternId, body: &Body) -> Self::Output {
        self.default_output(pattern_id, body)
    }

    /// Visit literal pattern
    fn visit_literal_pattern(&mut self, pattern_id: PatternId, body: &Body) -> Self::Output {
        self.default_output(pattern_id, body)
    }

    /// Visit binding pattern
    fn visit_binding(&mut self, pattern_id: PatternId, body: &Body) -> Self::Output {
        self.default_output(pattern_id, body)
    }

    /// Visit tuple pattern
    fn visit_tuple_pattern(
        &mut self,
        sub_patterns: &[PatternId],
        pattern_id: PatternId,
        body: &Body,
    ) -> Self::Output {
        for sub in sub_patterns {
            self.visit_pattern(*sub, body);
        }
        self.default_output(pattern_id, body)
    }

    /// Visit struct pattern
    fn visit_struct_pattern(
        &mut self,
        fields: &[(rv_intern::Symbol, PatternId)],
        pattern_id: PatternId,
        body: &Body,
    ) -> Self::Output {
        for (_, field_pattern) in fields {
            self.visit_pattern(*field_pattern, body);
        }
        self.default_output(pattern_id, body)
    }

    /// Visit enum pattern
    fn visit_enum_pattern(
        &mut self,
        sub_patterns: &[PatternId],
        pattern_id: PatternId,
        body: &Body,
    ) -> Self::Output {
        for sub in sub_patterns {
            self.visit_pattern(*sub, body);
        }
        self.default_output(pattern_id, body)
    }

    /// Visit or pattern
    fn visit_or_pattern(
        &mut self,
        alternatives: &[PatternId],
        pattern_id: PatternId,
        body: &Body,
    ) -> Self::Output {
        for alt in alternatives {
            self.visit_pattern(*alt, body);
        }
        self.default_output(pattern_id, body)
    }

    /// Visit range pattern
    fn visit_range_pattern(&mut self, pattern_id: PatternId, body: &Body) -> Self::Output {
        self.default_output(pattern_id, body)
    }

    /// Default output for a pattern (must be implemented)
    fn default_output(&mut self, pattern_id: PatternId, body: &Body) -> Self::Output;
}
