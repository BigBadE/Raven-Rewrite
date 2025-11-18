fn main() -> i64 {
    let x = if true {
        42
    } else {
        "string" //~ ERROR type mismatch in if-else branches
    };
    x
}
