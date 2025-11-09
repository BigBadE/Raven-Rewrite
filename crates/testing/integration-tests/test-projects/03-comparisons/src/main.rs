fn main() -> bool {
    5 < 10
}

#[test]
fn test_less_than() -> bool {
    if 5 < 10 {
        true
    } else {
        false
    }
}

#[test]
fn test_greater_than() -> bool {
    if 10 > 5 {
        true
    } else {
        false
    }
}

#[test]
fn test_less_equal() -> bool {
    if 5 <= 5 {
        if 5 <= 10 {
            true
        } else {
            false
        }
    } else {
        false
    }
}

#[test]
fn test_greater_equal() -> bool {
    if 10 >= 10 {
        if 10 >= 5 {
            true
        } else {
            false
        }
    } else {
        false
    }
}

#[test]
fn test_equality() -> bool {
    if 42 == 42 {
        true
    } else {
        false
    }
}

#[test]
fn test_inequality() -> bool {
    if 5 != 10 {
        true
    } else {
        false
    }
}
