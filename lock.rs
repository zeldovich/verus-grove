use vstd::{prelude::*};

verus! {
    // pub trait Predicate<A> {
    //     spec fn pred(a: A) -> bool;
    // }

    #[verifier::external_body]
    pub struct Lock< #[verifier::reject_recursive_types] A> {
        // mu: Arc<Mutex<A>>
        phantom: core::marker::PhantomData<A>,
    }

    // FIXME: implement this so the code is runnable
    impl<A> Lock<A> {

        pub spec fn getPred(self) -> FnSpec(A) -> bool;

        #[verifier::external_body]
        pub fn new(a:A, Ghost(pred):Ghost<FnSpec(A) -> bool>) -> (l:Lock<A>)
            requires pred(a)
            ensures l.getPred() == pred
            // ensures forall|a:A| l.pred(a) == pred(a)
        {
            // let data = Arc::new(Mutex::new(0));
            unimplemented!();
        }

        #[verifier::external_body]
        pub fn lock(&self) -> (a:A)
            ensures self.getPred()(a)
        {
            unimplemented!();
        }

        #[verifier::external_body]
        pub fn unlock(&self, a:A)
            requires self.getPred()(a)
        {
            unimplemented!();
        }
    }

    fn main() {}
} // verus!
