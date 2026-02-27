fn main() -> i64 {
    42
}

#[test]
fn test_int_to_float_to_int() -> bool {
    let x: i64 = 42;
    let y: f64 = x as f64;
    let z: i64 = y as i64;
    if z == 42 { true } else { false }
}

#[test]
fn test_bool_to_int() -> bool {
    let t: bool = true;
    let f: bool = false;
    let t_val: i64 = t as i64;
    let f_val: i64 = f as i64;
    if t_val == 1 {
        if f_val == 0 { true } else { false }
    } else {
        false
    }
}
