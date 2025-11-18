fn return_local_ref<'a>() -> &'a i64 {
    let x = 42;
    &x // Error: x doesn't outlive 'a
}

fn main() -> i64 {
    *return_local_ref()
}
