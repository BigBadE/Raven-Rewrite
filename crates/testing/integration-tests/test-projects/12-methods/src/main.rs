// Method syntax tests

struct Counter {
    value: i64,
}

impl Counter {
    fn get_value(self) -> i64 {
        self.value
    }

    fn doubled(self) -> i64 {
        self.value * 2
    }
}

struct Point {
    x: i64,
    y: i64,
}

impl Point {
    fn sum(self) -> i64 {
        self.x + self.y
    }

    fn scale(self, factor: i64) -> i64 {
        self.x * factor + self.y * factor
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
    let result = counter.doubled();
    if result == 20 { true } else { false }
}

#[test]
fn test_multi_field_method() -> bool {
    let p = Point { x: 3, y: 7 };
    let result = p.sum();
    if result == 10 { true } else { false }
}

#[test]
fn test_method_with_args() -> bool {
    let p = Point { x: 2, y: 3 };
    let result = p.scale(4);
    if result == 20 { true } else { false }
}
