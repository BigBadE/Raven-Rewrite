trait Display {
    fn display(&self) -> i64;
}

fn print_it<T: Display>(x: &T) -> i64 {
    x.display()
}

fn main() -> i64 {
    let x = 42;
    print_it(&x) // Error: i64 doesn't implement Display
}
