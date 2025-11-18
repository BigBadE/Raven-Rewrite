enum List {
    Cons(i64, Box<List>),
    Nil,
}

fn sum_list(list: &List) -> i64 {
    match list {
        List::Cons(x, rest) => x + sum_list(rest),
        List::Nil => 0,
    }
}

fn main() -> i64 {
    let list = List::Cons(10, Box::new(List::Cons(20, Box::new(List::Cons(12, Box::new(List::Nil))))));
    sum_list(&list)
}
