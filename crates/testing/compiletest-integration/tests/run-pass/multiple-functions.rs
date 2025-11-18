fn add(a: i64, b: i64) -> i64 {
    a + b
}

fn multiply(a: i64, b: i64) -> i64 {
    a * b
}

fn calculate() -> i64 {
    let sum = add(10, 20);
    let product = multiply(3, 4);
    sum + product
}

fn main() -> i64 {
    calculate()
}
