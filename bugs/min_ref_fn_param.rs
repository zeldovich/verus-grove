#![feature(prelude_import)]



#![allow(internal_features)]
#![feature(stmt_expr_attributes)]
#![feature(box_patterns)]
#![feature(negative_impls)]
#![feature(rustc_attrs)]
#![feature(unboxed_closures)]
#![feature(register_tool)]
#![feature(tuple_trait)]
#![feature(custom_inner_attributes)]
#![feature(try_trait_v2)]
#[prelude_import]
use std::prelude::rust_2018::*;
#[macro_use]
extern crate std;
use vstd::prelude::*;
use std::ops::Index;
#[verus::internal(verus_macro)]
pub struct Foo {
    x: u64,
}
#[verus::internal(verus_macro)]
fn test<'a>(f: &'a Foo) -> &'a u64 { return &f.x; }
#[verus::internal(verus_macro)]
fn test2(x: &[u64; 1]) -> &u64 { return &(x[0]); }
fn main() {}
