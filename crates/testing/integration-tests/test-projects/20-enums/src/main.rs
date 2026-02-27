enum Color {
    Red,
    Green,
    Blue,
}

fn color_value(c: Color) -> i64 {
    match c {
        Color::Red => 10,
        Color::Green => 20,
        Color::Blue => 30,
        _ => 0,
    }
}

fn main() -> i64 {
    42
}

#[test]
fn test_unit_variant_match() -> bool {
    let c = Color::Red;
    let result = match c {
        Color::Red => 10,
        _ => 0,
    };
    if result == 10 { true } else { false }
}

#[test]
fn test_green_variant() -> bool {
    let c = Color::Green;
    let result = match c {
        Color::Red => 1,
        Color::Green => 2,
        Color::Blue => 3,
        _ => 0,
    };
    if result == 2 { true } else { false }
}

#[test]
fn test_blue_variant() -> bool {
    let c = Color::Blue;
    let result = match c {
        Color::Red => 1,
        Color::Green => 2,
        Color::Blue => 3,
        _ => 0,
    };
    if result == 3 { true } else { false }
}

#[test]
fn test_enum_in_function() -> bool {
    let val = color_value(Color::Green);
    if val == 20 { true } else { false }
}
