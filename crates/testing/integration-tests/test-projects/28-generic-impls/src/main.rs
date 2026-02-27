trait Describable {
    fn describe(&self) -> i64;
}

struct Wrapper {
    inner: i64,
}

impl Describable for Wrapper {
    fn describe(&self) -> i64 {
        self.inner
    }
}

fn get_description<T: Describable>(item: &T) -> i64 {
    item.describe()
}

fn main() -> i64 {
    let w = Wrapper { inner: 55 };
    get_description(&w)
}
