struct Counter {
    value: i64,
}

impl Counter {
    fn get_value(self) -> i64 {
        self.value
    }
}

fn main() -> i64 {
    let counter = Counter { value: 5 };
    let result = counter.get_value();
    result
}
