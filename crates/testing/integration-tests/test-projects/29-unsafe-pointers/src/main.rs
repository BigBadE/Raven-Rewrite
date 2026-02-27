fn main() -> i64 {
    0
}

#[test]
fn test_unsafe_block_value() -> bool {
    let x: i64 = unsafe { 100 };
    if x == 100 { true } else { false }
}

#[test]
fn test_unsafe_block_computation() -> bool {
    let a: i64 = 10;
    let b: i64 = 20;
    let result: i64 = unsafe { a + b };
    if result == 30 { true } else { false }
}

#[test]
fn test_int_to_pointer_roundtrip() -> bool {
    let addr: i64 = 12345;
    let ptr: *const i64 = addr as *const i64;
    let back: i64 = ptr as i64;
    if back == 12345 { true } else { false }
}

#[test]
fn test_mut_pointer_roundtrip() -> bool {
    let addr: i64 = 99999;
    let ptr: *mut i64 = addr as *mut i64;
    let back: i64 = ptr as i64;
    if back == 99999 { true } else { false }
}

#[test]
fn test_pointer_to_pointer_cast() -> bool {
    let addr: i64 = 42;
    let p1: *const i64 = addr as *const i64;
    let p2: *const i64 = p1 as *const i64;
    let back: i64 = p2 as i64;
    if back == 42 { true } else { false }
}

#[test]
fn test_never_type_coercion() -> bool {
    let x: i64 = if true { 42 } else { loop {} };
    if x == 42 { true } else { false }
}
