enum List {
    Cons(i64, List), // Error: recursive type without indirection (needs Box)
    Nil,
}

fn main() -> i64 {
    let list = List::Nil;
    0
}
