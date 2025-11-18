fn classify_comprehensive(x: i64) -> i64 {
    match x {
        0 => 0,
        1 => 10,
        2 => 20,
        3 => 30,
        4 => 40,
        5 => 50,
        6..=10 => 60,
        11..=20 => 70,
        21..=100 => 80,
        _ => 90,
    }
}

fn main() -> i64 {
    classify_comprehensive(7)
}
