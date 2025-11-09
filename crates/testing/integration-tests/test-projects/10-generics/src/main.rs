fn identity<T>(x: T) -> T {
    x
}

fn max<T>(a: T, b: T) -> T {
    if a > b {
        a
    } else {
        b
    }
}

fn main() -> i64 {
    42
}

#[test]
fn test_identity() -> bool {
    if identity(42) == 42 {
        true
    } else {
        false
    }
}

#[test]
fn test_identity_different_value() -> bool {
    if identity(100) == 100 {
        true
    } else {
        false
    }
}

#[test]
fn test_max() -> bool {
    if max(10, 20) == 20 {
        true
    } else {
        false
    }
}

#[test]
fn test_max_reversed() -> bool {
    if max(20, 10) == 20 {
        true
    } else {
        false
    }
}

#[test]
fn test_max_equal() -> bool {
    if max(15, 15) == 15 {
        true
    } else {
        false
    }
}
