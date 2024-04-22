use vstd::{prelude::*,atomic::*,invariant::*};

verus! {

    enum LockResources<A> {
        Locked(Tracked<PermissionU64>, A),
        Unlocked(Tracked<PermissionU64>)
    }
    struct LockInv<A> {
        x: std::marker::PhantomData<A>,
    }

    impl<A> InvariantPredicate<(), A> for LockInv<A>
    {
        open spec fn inv(k:(), a:A) -> bool {
            true
        }
    }

    // Allowing recursive types is OK here because there should be no way to
    // construct an object of type
    // 
    // struct R {
    //     l: Lock<R>
    // }
    //
    // as one would want for proving false. This is not a proof, and this may
    // still be a bad assumption.
    #[verifier::external_body]
    #[verifier::reject_recursive_types(A)]
    pub struct Lock<A> {
        // phantom: core::marker::PhantomData<A>,
        // FIXME: going to run into trouble with having physical resources A
        // inside the AtomicInvariant.
        // atomic_inv: AtomicInvariant<(), LockResources<A>, LockInv<LockResources<A>>>,
        // locked: PAtomicU64,
        l : std::sync::Mutex<A>
    }

    impl<A> Lock<A> {

        pub spec fn get_pred(self) -> spec_fn(A) -> bool;

        #[verifier::external_body]
        pub fn new(a:A, Ghost(pred):Ghost<spec_fn(A) -> bool>) -> (l:Lock<A>)
            requires pred(a)
            ensures l.get_pred() == pred
            // ensures forall|a:A| l.pred(a) == pred(a)
        {
            return Lock{
                l: std::sync::Mutex::new(a)
            };
        }

        // XXX: could implement this by requiring physical stuff to by Copy, and
        // making ghost stuff separate.
        #[verifier::external_body]
        pub fn lock(&self) -> (a:A)
            ensures self.get_pred()(a)
        {
            unimplemented!()
            // *self.l.lock().unwrap()
        }

        #[verifier::external_body]
        pub fn unlock(&self, a:A)
            requires self.get_pred()(a)
        {
            unimplemented!();
        }
    }

    fn main() {}
} // verus!
