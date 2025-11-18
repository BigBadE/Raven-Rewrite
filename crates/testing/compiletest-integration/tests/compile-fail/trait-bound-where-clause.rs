trait Printable {
    fn print(&self) -> i64;
}

fn process<T>(item: &T) -> i64
where
    T: Printable,
{
    item.print()
}

fn main() -> i64 {
    let x = 42;
    process(&x) // Error: i64 doesn't satisfy Printable bound
}
