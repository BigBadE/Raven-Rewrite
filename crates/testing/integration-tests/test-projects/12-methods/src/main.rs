// Method syntax tests

struct Counter {
    value: i64,
}

impl Counter {
    fn get_value(self) -> i64 {
        self.value
    }

    fn increment(self) -> i64 {
        self.value
    }
}

fn main() -> i64 {
    let counter = Counter { value: 5 };
    let result = counter.get_value();
    result
}

#[test]
fn test_method_call() -> bool {
    let counter = Counter { value: 5 };
    let result = counter.get_value();
    if result == 5 { true } else { false }
}

#[test]
fn test_method_with_computation() -> bool {
    let counter = Counter { value: 10 };
    let result = counter.increment();
    if result == 10 { true } else { false }
}
