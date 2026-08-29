#![feature(rustc_private)]
#![feature(box_patterns)]

extern crate rustc_abi;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

mod memory_safety {
    pub mod dangling_pointer_tests;
    pub mod double_free_tests;
    pub mod modularity_tests;
    pub mod tsa_tests;
    pub mod use_after_free_tests;
}
