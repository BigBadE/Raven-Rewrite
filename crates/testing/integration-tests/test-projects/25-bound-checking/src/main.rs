trait Summable {
    fn sum(&self) -> i64;
}

struct Pair {
    a: i64,
    b: i64,
}

impl Summable for Pair {
    fn sum(&self) -> i64 {
        self.a + self.b
    }
}

fn get_sum<T: Summable>(item: &T) -> i64 {
    item.sum()
}

fn main() -> i64 {
    let p = Pair { a: 15, b: 27 };
    get_sum(&p)
}
