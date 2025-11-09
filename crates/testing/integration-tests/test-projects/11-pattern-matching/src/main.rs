// Pattern matching tests

fn main() -> i64 {
    42
}

// Test: Match 1 with arms in order [1, 2, _]
// Expected: 10
#[test]
fn test_match_1_ordered() -> bool {
    let result = match 1 {
        1 => 10,
        2 => 20,
        _ => 30,
    };
    if result == 10 { true } else { false }
}

// Test: Match 2 with arms in order [1, 2, _]
// Expected: 20
#[test]
fn test_match_2_ordered() -> bool {
    let result = match 2 {
        1 => 10,
        2 => 20,
        _ => 30,
    };
    if result == 20 { true } else { false }
}

// Test: Match 2 with arms in REVERSE order [2, 1, _]
// Expected: 20
#[test]
fn test_match_2_reversed() -> bool {
    let result = match 2 {
        2 => 20,
        1 => 10,
        _ => 30,
    };
    if result == 20 { true } else { false }
}

// Test: Match 99 (wildcard) with arms [1, 2, _]
// Expected: 30
#[test]
fn test_match_wildcard_ordered() -> bool {
    let result = match 99 {
        1 => 10,
        2 => 20,
        _ => 30,
    };
    if result == 30 { true } else { false }
}

// Test: Pattern binding - bind matched value to variable
// Expected: 42
#[test]
fn test_pattern_binding() -> bool {
    let result = match 42 {
        x => x,
    };
    if result == 42 { true } else { false }
}

// Test: Pattern binding with literal fallthrough
// Expected: 100 (matches binding pattern, not literal)
#[test]
fn test_pattern_binding_with_literal() -> bool {
    let result = match 100 {
        1 => 10,
        x => x,
    };
    if result == 100 { true } else { false }
}
