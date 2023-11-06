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

    #[verifier::external_body]
    pub struct Lock< #[verifier::reject_recursive_types] A> {
        // phantom: core::marker::PhantomData<A>,
        // FIXME: going to run into trouble with having physical resources A
        // inside the AtomicInvariant.
        atomic_inv: AtomicInvariant<(), LockResources<A>, LockInv<LockResources<A>>>,
        locked: PAtomicU64,
    }

    impl<A> Lock<A> {

        pub spec fn get_pred(self) -> FnSpec(A) -> bool;

        #[verifier::external_body]
        pub fn new(a:A, Ghost(pred):Ghost<FnSpec(A) -> bool>) -> (l:Lock<A>)
            requires pred(a)
            ensures l.get_pred() == pred
            // ensures forall|a:A| l.pred(a) == pred(a)
        {
            // let data = Arc::new(Mutex::new(0));
            unimplemented!();
        }

        #[verifier::external_body]
        pub fn lock(&self) -> (a:A)
            ensures self.get_pred()(a)
        {
            unimplemented!();
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
