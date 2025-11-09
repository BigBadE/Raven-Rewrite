//! Pattern exhaustiveness checking
//!
//! This module implements basic exhaustiveness checking for match expressions.

use crate::{Body, LiteralKind, MatchArm, Pattern, PatternId};
use std::collections::HashSet;

/// Check if a match expression is exhaustive
pub fn is_exhaustive(arms: &[MatchArm], body: &Body) -> ExhaustivenessResult {
    let mut has_wildcard = false;
    let mut literal_values = HashSet::new();
    let mut has_range_covering_all = false;

    for arm in arms {
        let pattern = &body.patterns[arm.pattern];
        match pattern {
            Pattern::Wildcard { .. } | Pattern::Binding { .. } => {
                has_wildcard = true;
                break; // Wildcard makes it exhaustive
            }
            Pattern::Literal { kind, .. } => {
                if let Some(val) = literal_to_value(kind) {
                    literal_values.insert(val);
                }
            }
            Pattern::Or { patterns, .. } => {
                // Check each alternative in the or-pattern
                for pat_id in patterns {
                    if let Pattern::Literal { kind, .. } = &body.patterns[*pat_id] {
                        if let Some(val) = literal_to_value(kind) {
                            literal_values.insert(val);
                        }
                    }
                }
            }
            Pattern::Range { start, end, inclusive, .. } => {
                // Check if range covers a significant portion
                if let (Some(s), Some(e)) = (literal_to_value(start), literal_to_value(end)) {
                    let range_size = if *inclusive { e - s + 1 } else { e - s };
                    // If range is very large (e.g., i64::MIN..=i64::MAX), consider it exhaustive
                    if range_size > 1_000_000 {
                        has_range_covering_all = true;
                    }
                }
            }
            Pattern::Tuple { .. } | Pattern::Struct { .. } | Pattern::Enum { .. } => {
                // For complex patterns, we'd need more sophisticated checking
                // For now, assume they require a wildcard
            }
        }
    }

    if has_wildcard || has_range_covering_all {
        ExhaustivenessResult::Exhaustive
    } else {
        ExhaustivenessResult::NonExhaustive {
            missing_patterns: vec!["_ (wildcard)".to_string()],
        }
    }
}

/// Result of exhaustiveness checking
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExhaustivenessResult {
    /// The match is exhaustive
    Exhaustive,
    /// The match is not exhaustive
    NonExhaustive {
        /// Examples of missing patterns
        missing_patterns: Vec<String>,
    },
}

fn literal_to_value(kind: &LiteralKind) -> Option<i64> {
    match kind {
        LiteralKind::Integer(val) => Some(*val),
        LiteralKind::Bool(b) => Some(if *b { 1 } else { 0 }),
        _ => None,
    }
}
