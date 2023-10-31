use vstd::{prelude::*};

verus! {
    pub trait Predicate<A> {
        spec fn pred(a: A) -> bool;
    }

    #[verifier::external_body]
    pub struct Lock< #[verifier::reject_recursive_types] A ,
                       #[verifier::reject_recursive_types] Pred:Predicate<A>> {
        // mu: Arc<Mutex<A>>
        phantom: core::marker::PhantomData<(A, Pred)>,
    }

    impl<A, Pred: Predicate<A>> Lock<A, Pred> {
        // FIXME: implement this so the code is runnable
        #[verifier::external_body]
        pub fn new(a:A) -> Lock<A, Pred>
            requires Pred::pred(a)
        {
            // let data = Arc::new(Mutex::new(0));
            unimplemented!();
        }

        #[verifier::external_body]
        pub fn lock(&self) -> (a:A)
            ensures Pred::pred(a)
        {
            unimplemented!();
        }

        #[verifier::external_body]
        pub fn unlock(&self, a:A)
            requires Pred::pred(a)
        {
            unimplemented!();
        }
    }

    fn main() {}
} // verus!
