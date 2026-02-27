fn main() -> i64 {
    42
}

#[test]
fn test_float_addition() -> bool {
    let a = 1.5;
    let b = 2.5;
    let c = a + b;
    if c == 4.0 { true } else { false }
}

#[test]
fn test_float_subtraction() -> bool {
    let a = 10.0;
    let b = 3.0;
    let c = a - b;
    if c == 7.0 { true } else { false }
}

#[test]
fn test_float_multiplication() -> bool {
    let a = 3.0;
    let b = 4.0;
    let c = a * b;
    if c == 12.0 { true } else { false }
}

#[test]
fn test_float_division() -> bool {
    let a = 10.0;
    let b = 4.0;
    let c = a / b;
    if c == 2.5 { true } else { false }
}

#[test]
fn test_float_negation() -> bool {
    let a = 5.0;
    let b = -a;
    if b == -5.0 { true } else { false }
}
