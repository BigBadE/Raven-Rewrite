trait Display {
    fn display(&self) -> i64;
}

impl Display for i64 {
    fn display(&self) -> i64 {
        *self
    }
}

fn show<T: Display>(x: &T) -> i64 {
    x.display()
}

fn main() -> i64 {
    let x = 42;
    show(&x)
}
