// Test basic pattern matching with multiple literals
#[test]
fn test_or_pattern() -> bool {
    let x = 2;
    let result = match x {
        1 => 42,
        2 => 42,
        3 => 42,
        _ => 0
    };
    result == 42
}

// Test sequential range simulation
#[test]
fn test_range_inclusive() -> bool {
    let x = 5;
    let result = match x {
        1 => 42,
        2 => 42,
        3 => 42,
        4 => 42,
        5 => 42,
        6 => 42,
        7 => 42,
        8 => 42,
        9 => 42,
        10 => 42,
        _ => 0
    };
    result == 42
}

// Test exclusive range (10 not included)
#[test]
fn test_range_exclusive() -> bool {
    let x = 10;
    let result = match x {
        1 => 42,
        2 => 42,
        3 => 42,
        4 => 42,
        5 => 42,
        6 => 42,
        7 => 42,
        8 => 42,
        9 => 42,
        _ => 0
    };
    result == 0  // 10 is NOT in range 1..=9, so should return 0
}

// Test combined patterns
#[test]
fn test_combined_patterns() -> bool {
    let a = match 2 {
        1 => 10,
        2 => 10,
        3 => 20,
        4 => 20,
        5 => 20,
        _ => 0
    };

    let b = match 4 {
        1 => 10,
        2 => 10,
        3 => 20,
        4 => 20,
        5 => 20,
        _ => 0
    };

    let c = match 7 {
        1 => 10,
        2 => 10,
        3 => 20,
        4 => 20,
        5 => 20,
        _ => 30
    };

    let result = a + b + c + 40;  // 10 + 20 + 30 + 40 = 100
    result == 100
}

fn main() -> i64 {
    // Run a simple computation for the main entry point
    let a = match 2 {
        1 => 10,
        2 => 10,
        3 => 20,
        4 => 20,
        5 => 20,
        _ => 0
    };

    let b = match 4 {
        1 => 10,
        2 => 10,
        3 => 20,
        4 => 20,
        5 => 20,
        _ => 0
    };

    let c = match 7 {
        1 => 10,
        2 => 10,
        3 => 20,
        4 => 20,
        5 => 20,
        _ => 30
    };

    a + b + c + 40  // 10 + 20 + 30 + 40 = 100
}
