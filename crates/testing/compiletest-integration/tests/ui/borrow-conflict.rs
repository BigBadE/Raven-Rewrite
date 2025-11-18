fn main() -> i64 {
    let mut x = 10;
    let r1 = &x;
    let r2 = &mut x; //~ ERROR cannot borrow as mutable while immutably borrowed
    *r2
}
