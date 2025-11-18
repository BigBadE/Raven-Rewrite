trait Addable {
    fn add(&self, other: &Self) -> Self;
}

struct Counter {
    value: i64,
}

impl Addable for Counter {
    fn add(&self, other: &Counter) -> Counter {
        Counter { value: self.value + other.value }
    }
}

fn main() -> i64 {
    let c1 = Counter { value: 20 };
    let c2 = Counter { value: 22 };
    let result = c1.add(&c2);
    result.value
}
