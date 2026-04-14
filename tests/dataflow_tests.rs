#![feature(rustc_private)]
#![feature(box_patterns)]

extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_target;

mod dataflow_tests {
    pub mod aliasing_tests;
    pub mod bw_flow_tests;
    pub mod handler_tests;
    pub mod fw_flow_tests;
}
