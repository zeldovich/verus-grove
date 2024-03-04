use vstd::{prelude::*, invariant::*};

verus! {
    pub struct Tok {}

    fn test0(x:[Tok; 8]) -> (ret:Tok) {
        return x[0];
    }

    proof fn test1(tracked x:[Tok; 8]) -> (tracked ret:Tok) {
        return x[0];
    }

    fn test2(x:Tracked<[Tok; 8]>) -> Tracked<Tok> {
        let tracked y; let tracked z;
        proof {
            y = x.get();
            z = y[0];
        }
        return Tracked(z);
    }

    fn test3(x:&[Tracked<Tok>; 8]) -> &Tracked<Tok> {
        return &(x[0]);
    }

    fn main() {}
} // verus!
