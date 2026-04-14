/// A simple double-free example.

fn trigger_double_free() {
    let mut v = vec![1, 2, 3];
    let ptr = v.as_mut_ptr();
    // Creates a second Vec that shares ownership of the same buffer.
    let _v2 = unsafe { 
        Vec::from_raw_parts(ptr, v.len(), v.capacity()) 
    };
    // Double-free: both `v` and `v2` will free the same allocation on drop.
}

fn main() {
    trigger_double_free();
}
