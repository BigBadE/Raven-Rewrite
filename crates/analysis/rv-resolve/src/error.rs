//! Error types for name resolution

use rv_intern::Symbol;
use rv_span::FileSpan;

/// Errors that occur during name resolution
#[derive(Debug, Clone, thiserror::Error)]
pub enum ResolutionError {
    /// Variable or function is not defined in any visible scope
    #[error("Undefined name at {use_site:?}")]
    Undefined {
        /// The name that was not found
        name: Symbol,
        /// Where the name was used
        use_site: FileSpan,
        /// Suggested similar names (for "did you mean?" messages)
        suggestions: Vec<Symbol>,
    },

    /// Name is defined multiple times in the same scope
    #[error("Duplicate definition at {second:?} (first defined at {first:?})")]
    DuplicateDefinition {
        /// The name that was redefined
        name: Symbol,
        /// First definition location
        first: FileSpan,
        /// Second definition location
        second: FileSpan,
    },

    /// Attempt to use a private item from outside its scope
    #[error("Private item at {def_site:?}, cannot be accessed at {use_site:?}")]
    PrivateItem {
        /// The name of the private item
        name: Symbol,
        /// Where the item was defined
        def_site: FileSpan,
        /// Where the item was accessed
        use_site: FileSpan,
    },
}

impl ResolutionError {
    /// Compute suggestions for undefined names using Levenshtein distance
    pub fn compute_suggestions(
        name: Symbol,
        interner: &rv_intern::Interner,
        available_names: &[Symbol],
    ) -> Vec<Symbol> {
        let target = interner.resolve(&name);
        let mut suggestions: Vec<(Symbol, usize)> = available_names
            .iter()
            .map(|&candidate| {
                let candidate_str = interner.resolve(&candidate);
                let distance = levenshtein_distance(&target, &candidate_str);
                (candidate, distance)
            })
            .filter(|(_, distance)| *distance <= 3) // Only suggest if distance is small
            .collect();

        suggestions.sort_by_key(|(_, distance)| *distance);
        suggestions.into_iter().take(3).map(|(sym, _)| sym).collect()
    }
}

/// Compute Levenshtein distance between two strings
fn levenshtein_distance(source: &str, target: &str) -> usize {
    let source_len = source.len();
    let target_len = target.len();

    if source_len == 0 {
        return target_len;
    }
    if target_len == 0 {
        return source_len;
    }

    let mut matrix = vec![vec![0; target_len + 1]; source_len + 1];

    // Initialize first row and column
    for idx in 0..=source_len {
        matrix[idx][0] = idx;
    }
    for jdx in 0..=target_len {
        matrix[0][jdx] = jdx;
    }

    // Fill the matrix
    for (idx, source_char) in source.chars().enumerate() {
        for (jdx, target_char) in target.chars().enumerate() {
            let cost = if source_char == target_char { 0 } else { 1 };
            matrix[idx + 1][jdx + 1] = (matrix[idx][jdx + 1] + 1)
                .min(matrix[idx + 1][jdx] + 1)
                .min(matrix[idx][jdx] + cost);
        }
    }

    matrix[source_len][target_len]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_levenshtein_distance() {
        assert_eq!(levenshtein_distance("", ""), 0);
        assert_eq!(levenshtein_distance("abc", "abc"), 0);
        assert_eq!(levenshtein_distance("abc", "def"), 3);
        assert_eq!(levenshtein_distance("kitten", "sitting"), 3);
        assert_eq!(levenshtein_distance("saturday", "sunday"), 3);
    }
}
