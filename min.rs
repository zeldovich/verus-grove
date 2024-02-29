use vstd::{prelude::*, invariant::*};

verus! {
    #[verifier(external_body)]
    pub fn foo<X, F: FnOnce(X) -> u64 >
        (au:F) -> (x:u64)
        requires forall |x| au.ensures(x, 10u64)

        // Also doesn't work to try (`F:FnWithSpecification<ArgType, Output = someType>`)
    {
        unimplemented!();
    }

    fn main() {}
} // verus!
