trait Addable {
    fn add(&self, other: &Self) -> Self;
}

struct Counter {
    value: i64,
}

impl Addable for Counter {
    fn add(&self, other: &Counter) -> i64 { // Error: wrong return type
        self.value + other.value
    }
}

fn main() -> i64 {
    let c1 = Counter { value: 10 };
    let c2 = Counter { value: 20 };
    c1.add(&c2)
}
