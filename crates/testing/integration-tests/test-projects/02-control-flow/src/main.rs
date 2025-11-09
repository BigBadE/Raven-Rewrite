fn main() -> i64 {
    if true {
        100
    } else {
        200
    }
}

#[test]
fn test_if_true() -> bool {
    if if true { 1 } else { 2 } == 1 {
        true
    } else {
        false
    }
}

#[test]
fn test_if_false() -> bool {
    if if false { 1 } else { 2 } == 2 {
        true
    } else {
        false
    }
}

#[test]
fn test_nested_if() -> bool {
    if if true {
        if false { 1 } else { 2 }
    } else {
        3
    } == 2 {
        true
    } else {
        false
    }
}

#[test]
fn test_if_with_arithmetic() -> bool {
    if if 10 > 5 { 100 } else { 200 } == 100 {
        true
    } else {
        false
    }
}
