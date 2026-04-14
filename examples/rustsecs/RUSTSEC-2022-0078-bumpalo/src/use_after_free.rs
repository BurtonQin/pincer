//! A use-after-free example
use crate::collections::Vec;
use crate::Bump;

extern crate std;

/// foo
pub fn foo<T>(_t: T) {}

/// main
pub fn main() {
    let bump = Bump::new();
    let mut vec = Vec::new_in(&bump);
    vec.extend([0x01u8; 32]);
    let into_iter = vec.into_iter();
    drop(bump);

    for _ in 0..100 {
        let reuse_bump = Bump::new();
        let _reuse_alloc = reuse_bump.alloc([0x41u8; 10]);
    }

    for x in into_iter {
        foo(x);
    }
}
