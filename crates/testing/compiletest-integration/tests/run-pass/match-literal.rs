fn classify(x: i64) -> i64 {
    match x {
        0 => 0,
        1 => 10,
        2 => 20,
        _ => 99,
    }
}

fn main() -> i64 {
    classify(2)
}
