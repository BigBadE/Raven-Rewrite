//! Pattern exhaustiveness checking
//!
//! This module implements full exhaustiveness checking for match expressions using
//! the pattern matrix algorithm.

use crate::{Body, EnumDef, LiteralKind, MatchArm, Pattern, PatternId, StructDef, TypeDefId, VariantFields};
use rv_intern::Symbol;
use std::collections::HashMap;

/// Check if a match expression is exhaustive
pub fn is_exhaustive(
    arms: &[MatchArm],
    body: &Body,
    structs: &HashMap<TypeDefId, StructDef>,
    enums: &HashMap<TypeDefId, EnumDef>,
) -> ExhaustivenessResult {
    // Build pattern matrix from match arms
    let mut matrix = PatternMatrix::new();

    for arm in arms {
        let pattern_row = vec![arm.pattern];
        matrix.add_row(pattern_row);
    }

    // Check for missing patterns
    let missing = compute_missing_patterns(&matrix, body, structs, enums);

    if missing.is_empty() {
        ExhaustivenessResult::Exhaustive
    } else {
        ExhaustivenessResult::NonExhaustive {
            missing_patterns: missing,
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

/// Constructor representation for pattern matching
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Constructor {
    /// Enum variant with name and field count
    Variant { name: Symbol, arity: usize },
    /// Tuple with field count
    Tuple { arity: usize },
    /// Struct with fields
    Struct { name: Symbol, fields: Vec<Symbol> },
    /// Integer range (inclusive)
    IntRange { start: i64, end: i64 },
    /// Boolean value
    Bool(bool),
    /// Wildcard matches anything
    Wildcard,
}

impl Constructor {
    /// Get all constructors for a given type
    fn all_for_type(
        type_def_id: Option<TypeDefId>,
        structs: &HashMap<TypeDefId, StructDef>,
        enums: &HashMap<TypeDefId, EnumDef>,
    ) -> Vec<Self> {
        if let Some(def_id) = type_def_id {
            // Check if it's an enum
            if let Some(enum_def) = enums.get(&def_id) {
                return enum_def
                    .variants
                    .iter()
                    .map(|variant| {
                        let arity = match &variant.fields {
                            VariantFields::Unit => 0,
                            VariantFields::Tuple(fields) => fields.len(),
                            VariantFields::Struct(fields) => fields.len(),
                        };
                        Constructor::Variant {
                            name: variant.name,
                            arity,
                        }
                    })
                    .collect();
            }

            // Check if it's a struct
            if let Some(struct_def) = structs.get(&def_id) {
                return vec![Constructor::Struct {
                    name: struct_def.name,
                    fields: struct_def.fields.iter().map(|f| f.name).collect(),
                }];
            }
        }

        // For other types, wildcard is the only constructor
        vec![Constructor::Wildcard]
    }

    /// Get the arity (number of sub-patterns) for this constructor
    fn arity(&self) -> usize {
        match self {
            Constructor::Variant { arity, .. } => *arity,
            Constructor::Tuple { arity } => *arity,
            Constructor::Struct { fields, .. } => fields.len(),
            Constructor::IntRange { .. } | Constructor::Bool(_) | Constructor::Wildcard => 0,
        }
    }
}

/// Pattern matrix for exhaustiveness checking
struct PatternMatrix {
    rows: Vec<Vec<PatternId>>,
}

impl PatternMatrix {
    fn new() -> Self {
        Self { rows: Vec::new() }
    }

    fn add_row(&mut self, row: Vec<PatternId>) {
        self.rows.push(row);
    }

    fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// Specialize the matrix for a given constructor
    fn specialize(
        &self,
        constructor: &Constructor,
        body: &Body,
    ) -> PatternMatrix {
        let mut specialized = PatternMatrix::new();

        for row in &self.rows {
            if row.is_empty() {
                continue;
            }

            let first_pat = &body.patterns[row[0]];
            let rest = &row[1..];

            match first_pat {
                Pattern::Wildcard { .. } | Pattern::Binding { .. } => {
                    // Wildcard expands to constructor arity wildcards
                    let mut new_row = vec![row[0]; constructor.arity()];
                    new_row.extend_from_slice(rest);
                    specialized.add_row(new_row);
                }
                Pattern::Enum { variant, sub_patterns, def, .. } => {
                    if let Constructor::Variant { name, .. } = constructor {
                        if variant == name {
                            let mut new_row = sub_patterns.clone();
                            new_row.extend_from_slice(rest);
                            specialized.add_row(new_row);
                        }
                    }
                }
                Pattern::Struct { fields, ty, .. } => {
                    if let Constructor::Struct { name, fields: expected_fields, .. } = constructor {
                        // Match struct patterns
                        let mut new_row = Vec::new();
                        for expected_field in expected_fields {
                            if let Some(field_pat) = fields.iter().find(|f| f.0 == *expected_field) {
                                new_row.push(field_pat.1);
                            } else {
                                // Missing field treated as wildcard
                                new_row.push(row[0]);
                            }
                        }
                        new_row.extend_from_slice(rest);
                        specialized.add_row(new_row);
                    }
                }
                Pattern::Tuple { patterns, .. } => {
                    if let Constructor::Tuple { arity } = constructor {
                        if patterns.len() == *arity {
                            let mut new_row = patterns.clone();
                            new_row.extend_from_slice(rest);
                            specialized.add_row(new_row);
                        }
                    }
                }
                Pattern::Literal { kind, .. } => {
                    match (kind, constructor) {
                        (LiteralKind::Integer(val), Constructor::IntRange { start, end }) => {
                            if val >= start && val <= end {
                                specialized.add_row(rest.to_vec());
                            }
                        }
                        (LiteralKind::Bool(b), Constructor::Bool(cb)) => {
                            if b == cb {
                                specialized.add_row(rest.to_vec());
                            }
                        }
                        _ => {}
                    }
                }
                Pattern::Range { start, end, inclusive, .. } => {
                    if let (Some(s), Some(e)) = (literal_to_value(start), literal_to_value(end)) {
                        let pattern_end = if *inclusive { e } else { e - 1 };
                        if let Constructor::IntRange { start: c_start, end: c_end } = constructor {
                            // Check if ranges overlap
                            if s <= *c_end && pattern_end >= *c_start {
                                specialized.add_row(rest.to_vec());
                            }
                        }
                    }
                }
                Pattern::Or { patterns, .. } => {
                    // Expand or-pattern alternatives
                    for pat_id in patterns {
                        let mut new_row = vec![*pat_id];
                        new_row.extend_from_slice(rest);
                        specialized.add_row(new_row);
                    }
                }
            }
        }

        specialized
    }

    /// Get default matrix (rows starting with wildcard/binding)
    fn default_matrix(&self, body: &Body) -> PatternMatrix {
        let mut default = PatternMatrix::new();

        for row in &self.rows {
            if row.is_empty() {
                continue;
            }

            let first_pat = &body.patterns[row[0]];
            match first_pat {
                Pattern::Wildcard { .. } | Pattern::Binding { .. } => {
                    if row.len() > 1 {
                        default.add_row(row[1..].to_vec());
                    } else {
                        default.add_row(Vec::new());
                    }
                }
                Pattern::Or { patterns, .. } => {
                    // Expand or-pattern
                    for pat_id in patterns {
                        let first_pat = &body.patterns[*pat_id];
                        if matches!(first_pat, Pattern::Wildcard { .. } | Pattern::Binding { .. }) {
                            if row.len() > 1 {
                                default.add_row(row[1..].to_vec());
                            } else {
                                default.add_row(Vec::new());
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        default
    }
}

/// Compute missing patterns using the pattern matrix algorithm
fn compute_missing_patterns(
    matrix: &PatternMatrix,
    body: &Body,
    structs: &HashMap<TypeDefId, StructDef>,
    enums: &HashMap<TypeDefId, EnumDef>,
) -> Vec<String> {
    // Base cases
    if matrix.rows.is_empty() {
        // No patterns matched - everything is missing
        return vec!["_".to_string()];
    }

    // Check if first column has a non-wildcard pattern
    let first_patterns: Vec<_> = matrix
        .rows
        .iter()
        .filter_map(|row| row.first())
        .collect();

    if first_patterns.is_empty() {
        // All rows are empty - check is complete
        return Vec::new();
    }

    // Find the type of the first pattern (if available)
    let type_def_id = first_patterns
        .iter()
        .find_map(|&&pat_id| {
            let pattern = &body.patterns[pat_id];
            match pattern {
                Pattern::Enum { def, .. } => *def,
                Pattern::Struct { .. } => None, // Type resolution would need additional context
                _ => None,
            }
        });

    // Get all possible constructors for this type
    let constructors = Constructor::all_for_type(type_def_id, structs, enums);

    // Check each constructor
    let mut missing = Vec::new();

    for constructor in &constructors {
        let specialized = matrix.specialize(constructor, body);

        if specialized.is_empty() {
            // This constructor is not covered
            match constructor {
                Constructor::Variant { name, .. } => {
                    missing.push(format!("{:?}(..)", name));
                }
                Constructor::Struct { name, .. } => {
                    missing.push(format!("{:?} {{ .. }}", name));
                }
                Constructor::Tuple { arity } => {
                    missing.push(format!("({})", "_,".repeat(*arity).trim_end_matches(',')));
                }
                Constructor::IntRange { start, end } => {
                    if start == end {
                        missing.push(format!("{}", start));
                    } else {
                        missing.push(format!("{}..={}", start, end));
                    }
                }
                Constructor::Bool(b) => {
                    missing.push(format!("{}", b));
                }
                Constructor::Wildcard => {
                    missing.push("_".to_string());
                }
            }
        } else {
            // Recursively check specialized matrix
            let sub_missing = compute_missing_patterns(&specialized, body, structs, enums);
            for sub in sub_missing {
                let prefix = match constructor {
                    Constructor::Variant { name, .. } => format!("{:?}({})", name, sub),
                    Constructor::Struct { name, .. } => format!("{:?} {{ {} }}", name, sub),
                    Constructor::Tuple { .. } => format!("({})", sub),
                    _ => sub,
                };
                missing.push(prefix);
            }
        }
    }

    // Check default matrix (for wildcards)
    if !matrix.default_matrix(body).is_empty() {
        let default_missing = compute_missing_patterns(&matrix.default_matrix(body), body, structs, enums);
        missing.extend(default_missing);
    }

    missing
}

fn literal_to_value(kind: &LiteralKind) -> Option<i64> {
    match kind {
        LiteralKind::Integer(val) => Some(*val),
        LiteralKind::Bool(b) => Some(if *b { 1 } else { 0 }),
        _ => None,
    }
}
