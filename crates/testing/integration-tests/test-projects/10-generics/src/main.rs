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
    if identity::<i64>(42) == 42 {
        true
    } else {
        false
    }
}

#[test]
fn test_identity_different_value() -> bool {
    if identity::<i64>(100) == 100 {
        true
    } else {
        false
    }
}

#[test]
fn test_max() -> bool {
    if max::<i64>(10, 20) == 20 {
        true
    } else {
        false
    }
}

#[test]
fn test_max_reversed() -> bool {
    if max::<i64>(20, 10) == 20 {
        true
    } else {
        false
    }
}

#[test]
fn test_max_equal() -> bool {
    if max::<i64>(15, 15) == 15 {
        true
    } else {
        false
    }
}
