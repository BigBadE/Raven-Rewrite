fn double_value(x: i64) -> i64 {
    match x {
        0 => 0,
        n => n * 2,
    }
}

fn main() -> i64 {
    double_value(21)
}
