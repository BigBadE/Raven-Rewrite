//! Compile-time constant evaluation
//!
//! This crate provides compile-time evaluation of constant expressions.
//! Used for:
//! - Array sizes: `[T; N]` where N is a const expression
//! - Const generic parameters
//! - Const item initializers: `const FOO: i64 = expr;`
//! - Static initializers: `static BAR: i64 = expr;`

mod error;
mod evaluator;
mod value;

pub use error::ConstError;
pub use evaluator::ConstEvaluator;
pub use value::ConstValue;

use rv_hir::{ConstId, ConstItem, StaticId, StaticItem};
use rv_intern::Interner;
use std::collections::HashMap;

/// Evaluate all const items, returning a map from ConstId to evaluated value.
///
/// Items are evaluated in iteration order. Later consts can reference earlier
/// ones (e.g., `const B: i64 = A + 1;` works if A was evaluated first).
pub fn evaluate_const_items(
    const_items: &HashMap<ConstId, ConstItem>,
    interner: &Interner,
) -> HashMap<ConstId, ConstValue> {
    let mut evaluator = ConstEvaluator::new_with_interner(interner.clone());
    let mut evaluated = HashMap::new();

    // Use fixed-point iteration: HashMap iteration order is non-deterministic,
    // so a const referencing another const may be visited before its dependency.
    // We keep trying until either all items are evaluated or no progress is made.
    let mut remaining: Vec<_> = const_items.keys().copied().collect();
    loop {
        let mut made_progress = false;
        let mut still_remaining = Vec::new();
        for const_id in &remaining {
            let const_item = &const_items[const_id];
            let root_expr = &const_item.body.exprs[const_item.body.root_expr];
            match evaluator.eval_expr(root_expr, &const_item.body) {
                Ok(value) => {
                    let name = interner.resolve(&const_item.name).to_string();
                    evaluator.register_const(name, value.clone());
                    evaluated.insert(*const_id, value);
                    made_progress = true;
                }
                Err(_) => {
                    still_remaining.push(*const_id);
                }
            }
        }
        remaining = still_remaining;
        if remaining.is_empty() || !made_progress {
            break;
        }
    }

    // Report errors for any items that could not be evaluated
    for const_id in &remaining {
        let const_item = &const_items[const_id];
        let root_expr = &const_item.body.exprs[const_item.body.root_expr];
        if let Err(e) = evaluator.eval_expr(root_expr, &const_item.body) {
            eprintln!("error[const-eval]: {e}");
        }
    }

    evaluated
}

/// Evaluate all static item initializers, returning a map from StaticId to evaluated value.
///
/// Static initializers must be compile-time evaluable. Previously evaluated const
/// values are available for reference in static initializers.
pub fn evaluate_static_items(
    static_items: &HashMap<StaticId, StaticItem>,
    const_items: &HashMap<ConstId, ConstItem>,
    const_values: &HashMap<ConstId, ConstValue>,
    interner: &Interner,
) -> HashMap<StaticId, ConstValue> {
    let mut evaluator = ConstEvaluator::new_with_interner(interner.clone());
    // Register all const values so static initializers can reference them
    for (const_id, value) in const_values {
        if let Some(const_item) = const_items.get(const_id) {
            let name = interner.resolve(&const_item.name).to_string();
            evaluator.register_const(name, value.clone());
        }
    }
    let mut evaluated = HashMap::new();
    for (static_id, static_item) in static_items {
        let root_expr = &static_item.body.exprs[static_item.body.root_expr];
        match evaluator.eval_expr(root_expr, &static_item.body) {
            Ok(value) => {
                evaluated.insert(*static_id, value);
            }
            Err(e) => eprintln!("error[const-eval]: {e}"),
        }
    }
    evaluated
}
