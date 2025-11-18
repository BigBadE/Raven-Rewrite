fn takes_int(x: i64) -> i64 {
    x
}

fn main() -> i64 {
    takes_int("hello") //~ ERROR type mismatch
}
