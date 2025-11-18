trait Display {
    fn display(&self) -> i64;
}

trait DebugDisplay: Display {
    fn debug_display(&self) -> i64;
}

impl Display for i64 {
    fn display(&self) -> i64 {
        *self
    }
}

impl DebugDisplay for i64 {
    fn debug_display(&self) -> i64 {
        self.display()
    }
}

fn show_debug<T: DebugDisplay>(x: &T) -> i64 {
    x.debug_display()
}

fn main() -> i64 {
    let x = 42;
    show_debug(&x)
}
