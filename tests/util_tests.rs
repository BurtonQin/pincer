#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_middle;

mod util_tests {
    pub mod axm_tests;
    pub mod drop_shim_tests;
    pub mod multimap_tests;
    pub mod rustc_type_tests;
}
