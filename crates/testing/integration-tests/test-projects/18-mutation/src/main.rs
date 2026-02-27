struct Point {
    x: i64,
    y: i64,
}

fn main() -> i64 {
    let mut p = Point { x: 1, y: 2 };
    p.x = 10;
    p.x + p.y
}

#[test]
fn test_struct_field_write() -> bool {
    let mut p = Point { x: 0, y: 0 };
    p.x = 42;
    if p.x == 42 { true } else { false }
}

#[test]
fn test_struct_both_fields_write() -> bool {
    let mut p = Point { x: 1, y: 2 };
    p.x = 10;
    p.y = 20;
    if p.x + p.y == 30 { true } else { false }
}

#[test]
fn test_struct_field_overwrite() -> bool {
    let mut p = Point { x: 100, y: 200 };
    p.x = 5;
    p.x = 10;
    if p.x == 10 { true } else { false }
}
