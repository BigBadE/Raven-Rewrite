struct Point {
    x: i32,
    y: i32,
}

fn main() -> i32 {
    let p = Point { x: 10, y: 20 };
    let result = p.x + p.y;
    if result == 30 { 1 } else { 0 }
}

#[test]
fn test_struct_creation() -> bool {
    let p = Point { x: 10, y: 20 };
    let result = p.x + p.y;
    if result == 30 { true } else { false }
}

#[test]
fn test_struct_field_access() -> bool {
    let p = Point { x: 42, y: 0 };
    if p.x == 42 { true } else { false }
}
