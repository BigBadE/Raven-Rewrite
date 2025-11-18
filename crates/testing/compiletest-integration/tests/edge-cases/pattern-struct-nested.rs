struct Point {
    x: i64,
    y: i64,
}

struct Container {
    point: Point,
    value: i64,
}

fn extract_all(c: Container) -> i64 {
    match c {
        Container { point: Point { x, y }, value } => x + y + value,
    }
}

fn main() -> i64 {
    let c = Container {
        point: Point { x: 10, y: 20 },
        value: 12,
    };
    extract_all(c)
}
