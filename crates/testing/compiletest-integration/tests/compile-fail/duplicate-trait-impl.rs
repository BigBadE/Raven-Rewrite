trait Display {
    fn display(&self) -> i64;
}

impl Display for i64 {
    fn display(&self) -> i64 { *self }
}

impl Display for i64 { // Error: duplicate trait implementation
    fn display(&self) -> i64 { *self + 1 }
}

fn main() -> i64 {
    42.display()
}
