struct Counter {
    value: i64,
}

impl Counter {
    fn get_value(self) -> i64 {
        self.value
    }
}

fn main() -> i64 {
    let c = Counter { value: 5 };
    let r = c.get_value();
    r
}
