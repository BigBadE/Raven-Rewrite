struct Counter {
    value: i64,
}

impl Counter {
    fn get_value(&self) -> i64 {
        self.value
    }
}

fn main() -> i64 {
    let c = Counter { value: 42 };
    c.get_value()
}
