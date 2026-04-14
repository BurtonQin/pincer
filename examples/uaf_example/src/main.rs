/// A simple use-after-free example.

fn from_string() -> Vec<u8> {
    let mut s = String::from("hello");
    let ptr = s.as_mut_ptr();
    // Creates a second Vec that shares ownership of the same buffer.
    let v = unsafe { 
        Vec::from_raw_parts(ptr, s.len(), s.capacity()) 
    };
    v
}

fn trigger_uaf() {
    let v = from_string();
    // Use-after-free: `v` points to freed memory since `s` has been 
    // dropped at the end of `from_string`.
    println!("{:?}", v);
}

fn main() {
    trigger_uaf();
}
