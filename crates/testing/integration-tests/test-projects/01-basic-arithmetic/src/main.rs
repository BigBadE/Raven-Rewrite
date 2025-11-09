fn main() -> i64 {
    42
}

#[test]
fn test_addition() -> bool {
    if 10 + 20 == 30 {
        true
    } else {
        false
    }
}

#[test]
fn test_subtraction() -> bool {
    if 50 - 20 == 30 {
        true
    } else {
        false
    }
}

#[test]
fn test_multiplication() -> bool {
    if 6 * 7 == 42 {
        true
    } else {
        false
    }
}

#[test]
fn test_division() -> bool {
    if 100 / 5 == 20 {
        true
    } else {
        false
    }
}

#[test]
fn test_complex_expression() -> bool {
    if 2 + 3 * 4 == 14 {
        true
    } else {
        false
    }
}
