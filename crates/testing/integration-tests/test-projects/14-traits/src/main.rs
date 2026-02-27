// Basic trait system test

trait Addable {
    fn add_value(&self, other: i64) -> i64;
}

struct Counter {
    value: i64,
}

impl Addable for Counter {
    fn add_value(&self, other: i64) -> i64 {
        self.value + other
    }
}

impl Counter {
    fn get_value(&self) -> i64 {
        self.value
    }
}

fn main() -> i64 {
    let c = Counter { value: 10 };
    let result = c.add_value(32);
    if result == 42 { 42 } else { 0 }
}

#[test]
fn test_trait_method() -> bool {
    let c = Counter { value: 10 };
    let result = c.add_value(32);
    if result == 42 { true } else { false }
}

#[test]
fn test_inherent_method() -> bool {
    let c = Counter { value: 7 };
    let result = c.get_value();
    if result == 7 { true } else { false }
}
