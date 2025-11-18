fn main() -> i64 {
    let x: i64 = 42;
    match x {
        "string" => 1, //~ ERROR type mismatch in pattern
        _ => 0,
    }
}
