use vstd::{prelude::*,invariant::*,thread::*};
mod lock;
mod kv;
use kv::*;

verus! {
    #[verifier(external_body)]
    #[verifier::reject_recursive_types(T)]
    pub struct SavedProp<T> {
        _unused:std::marker::PhantomData<T>,
    }

    impl<P> SavedProp<P> {
        spec fn gname() -> nat;

        #[verifier(external_body)]
        proof fn update<Q>(self) -> SavedProp<Q>
        {
            unimplemented!();
        }

        #[verifier(external_body)]
        proof fn agree<Q>(&self, other:&SavedProp<Q>) -> bool
            // XXX: want to return (Q ∗={∅}=∗ P), which requires trait objects.
            // FIXME: need (£ 1) as input, or return a higher-order function
            // □(£ 1 -∗ (Q ∗={∅}=∗ P))
        {
            unimplemented!();
        }
    }

    pub trait AtomicUpdate<Ag, At, Rg, Rt> {
        spec fn requires(&self, ag:Ag, at:At) -> bool;
        spec fn ensures(&self, ag:Ag, at:At, rg:Rg, rt:Rt) -> bool;
        proof fn call_once(tracked self, ag:Ag, tracked at:At) -> (tracked r:(Ghost<Rg>, Tracked<Rt>)) where Self: std::marker::Sized
            requires self.requires(ag, at)
            ensures self.ensures(ag, at, r.0@, r.1@);
            // opens_invariants any
    }

    // possible `state`s
    const UNUSED: u64 = 0;
    const ACTIVE: u64 = 1;

    // match state {
    //  
    // }
    struct WriteRequest {
        val:u64,
        state:u64, // see above for possible values
    }

    type RequestResources<P> = Box<dyn AtomicUpdate<u64, P, (), P>>;

    // sort-of a "flat combining" register, but with no lock-free accesses and a
    // publication list of length 1.
    #[verifier::reject_recursive_types(P)]
    pub struct Register<C, P, Pred> {
        plist: lock::Lock<(WriteRequest, Tracked<Option<RequestResources<P>>>)>,
        val: lock::Lock<(u64, Tracked<P>)>,
        _1:std::marker::PhantomData<Pred>,
        _2:std::marker::PhantomData<C>,
    }

    spec fn gen_val_pred<C, P, Pred: InvariantPredicate<C, (u64, P)>>(c:C) ->
        FnSpec((u64, Tracked<P>)) -> bool {
        |args:(u64, Tracked<_>)| -> bool {
            let (val, p) = args;
            Pred::inv(c, (val, p@))
        }
    }

    spec fn gen_plist_pred() -> FnSpec(WriteRequest) -> bool {
        |req:WriteRequest| {
            true
        }
    }

    impl<C, P, Pred: InvariantPredicate<C, (u64, P)>> Register<C, P, Pred> {
        spec fn constant(self) -> C;

        spec fn inv(self) -> bool {
            self.val.get_pred() == gen_val_pred::<C,P,Pred>(self.constant()) &&
            self.plist.get_pred() == gen_plist_pred()
        }

        // background thread that executes operations requested by other threads.
        fn combiner(&self)
            requires self.inv()
        {
            loop
                invariant self.inv()
            {
                let (req, Tracked(res)) = self.plist.lock();
                if req.state == ACTIVE {
                    let (oldval, Tracked(p)) = self.val.lock();
                    // FIXME: fire fupd
                    self.val.unlock((req.val, Tracked(p)));
                }
                self.plist.unlock((req, Tracked(None)));
            }
        }

        // requires (∀ v, P v ={∅}=∗ P v ∗ Φ)
        // ensures Φ
        fn read
            <Phi, Au:AtomicUpdate<u64, P, (), (P, Phi)>>
            (&self, Tracked(au):Tracked<Au>,
             phi_pred: FnSpec(u64, Phi) -> bool
            ) -> (ret:(u64, Tracked<Phi>))
            requires self.inv(),
            (forall |v:u64, p:P|
                Pred::inv(self.constant(), (v, p)) ==> #[trigger] au.requires(v, p)),

            (forall |v:u64, p:P, p_prime:P, phi:Phi|
             #[trigger] au.ensures(v, p, (), (p_prime, phi)) ==>
             Pred::inv(self.constant(), (v, p_prime)) &&
             phi_pred(v, phi))

            ensures phi_pred(ret.0,ret.1@)
        {
            let (v, Tracked(p)) = self.val.lock();
            let tracked (p, phi) = au.call_once(v,p).1.get();
            self.val.unlock((v, Tracked(p)));
            return (v, Tracked(phi));
        }

        // requires (∀ oldv, P oldv ={∅}=∗ P v)
        // ensures True
        fn async_write(&self, v:u64)
            requires self.inv()
        {
            let mut req:WriteRequest;
            let tracked res;
            // wait for publication list to have an unused slot
            loop {
                let inner = self.plist.lock();
                req = inner.0;
                res = inner.1.get();

                if req.state == UNUSED {
                    break
                }
                self.plist.unlock((req, Tracked(res)));
            }

            // send request
            req.state = ACTIVE;
            req.val = v;
            self.plist.unlock((req, Tracked(res)));

            // XXX: this doesn't wait for a response. If it did wait, the spec
            // ought to return some user-chosen Φ that shows up on the RHS of
            // the atomic fupd. But, we'd need to use something like SavedProp
            // (potentially implemented with invariants) to show that when
            // we re-acquire the lock, the Φ in the lock invariant matches the
            // one we expect. That distracts from helping.
        }
    }

    fn main() {
    }
} // verus!
