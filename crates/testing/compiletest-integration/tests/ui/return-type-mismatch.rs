fn returns_wrong_type() -> i64 {
    "string" //~ ERROR type mismatch
}

fn main() -> i64 {
    returns_wrong_type()
}
