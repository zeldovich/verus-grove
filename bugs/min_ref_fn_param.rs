extern crate std;

use vstd::prelude::*;
use std::ops::Index;

verus!{
fn fails(x: &[u64; 1]) -> &u64 { return &(x[0]); }

fn main() {}
}

fn succeeds(x: &[u64; 1]) -> &u64 { return &(x[0]); }
