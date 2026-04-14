use CSemiBox;
use std::ops::Deref;

pub fn main() {
    let mut v = vec![1, 2, 3];
    let p = v.as_mut_ptr();
    let semibox: CSemiBox<'static, str> = CSemiBox::new(p as _);
    drop(semibox);
    println!("Hello World")
}