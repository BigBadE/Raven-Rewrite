trait Add {
    fn add(&self, other: &Self) -> Self;
}

struct Vec2 {
    x: i64,
    y: i64,
}

impl Add for Vec2 {
    fn add(&self, other: &Vec2) -> Vec2 {
        Vec2 {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}

fn main() -> i64 {
    let a = Vec2 { x: 10, y: 20 };
    let b = Vec2 { x: 3, y: 4 };
    let c = a + b;
    c.x + c.y
}
