use vstd::{prelude::*,invariant::*,thread::*};
mod lock;
mod kv;
use kv::*;

verus! {
    pub trait AtomicUpdate<Ag, At, Rg, Rt> {
        spec fn requires(&self, ag:Ag, at:At) -> bool;
        spec fn ensures(&self, ag:Ag, at:At, rg:Rg, rt:Rt) -> bool;
        proof fn call_once(tracked self, ag:Ag, tracked at:At) -> (tracked r:(Ghost<Rg>, Tracked<Rt>)) where Self: std::marker::Sized
            requires self.requires(ag, at)
            ensures self.ensures(ag, at, r.0@, r.1@);
            // opens_invariants any
    }

    // XXX: this is manually written model for `dyn AtomicUpdate...`
    #[verifier(external_body)]
    #[verifier::reject_recursive_types(Ag)]
    #[verifier::reject_recursive_types(At)]
    #[verifier::reject_recursive_types(Rg)]
    #[verifier::reject_recursive_types(Rt)]
    #[allow(non_camel_case_types)]
    struct _Dyn_AtomicUpdate<Ag, At, Rg, Rt> {
        _unused1: std::marker::PhantomData<Ag>,
        _unused2: std::marker::PhantomData<At>,
        _unused3: std::marker::PhantomData<Rg>,
        _unused4: std::marker::PhantomData<Rt>,
    }

    impl<Ag,At,Rg,Rt> _Dyn_AtomicUpdate<Ag,At,Rg,Rt> {
        #[verifier(external_body)]
        proof fn box_from<T:AtomicUpdate<Ag,At,Rg,Rt>>(t:T) -> (tracked ret:Box<Self>)
            // XXX: how does this fit into a model for `dyn T`?
            ensures
                (forall |ag, at| #[trigger] ret.requires(ag,at) == t.requires(ag,at)),
                (forall |ag, at, rg, rt| #[trigger] ret.ensures(ag,at,rg,rt) == t.ensures(ag,at,rg,rt))
        {
            unimplemented!();
        }
    }

    impl<Ag,At,Rg,Rt> AtomicUpdate<Ag,At,Rg,Rt> for _Dyn_AtomicUpdate<Ag,At,Rg,Rt> {
        spec fn requires(&self, ag:Ag, at:At) -> bool;
        spec fn ensures(&self, ag:Ag, at:At, rg:Rg, rt:Rt) -> bool;
        #[verifier(external_body)]
        proof fn call_once(tracked self, ag:Ag, tracked at:At) -> (tracked r:(Ghost<Rg>, Tracked<Rt>)) where Self: std::marker::Sized
        {
            unimplemented!();
        }
    }

    // XXX: end of model for `dyn AtomicUpdate`

    // possible `state`s
    const UNUSED: u64 = 0;
    const ACTIVE: u64 = 1;

    struct WriteRequest {
        val:u64,
        state:u64, // see above for possible values
    }

    // type RequestResources<P> = Box<dyn AtomicUpdate<u64, P, (), P>>;
    type RequestResources<P> = Box<_Dyn_AtomicUpdate<u64, P, (), P>>;

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

    // FIXME: want to write this as a match statement with forall's inside of
    // it, but then we can't set triggers as we want. Maybe introduce an
    // abstraction of a "valid fupd"?
    spec fn gen_plist_pred<C,P,Pred:InvariantPredicate<C, (u64, P)>>(c:C) ->
        FnSpec((WriteRequest, Tracked<Option<RequestResources<P>>>)) -> bool {
            // XXX: why so is much type annotation needed?
        |args: (WriteRequest, Tracked<Option<RequestResources<P>>>)| {
            ((args.1@ == None::<RequestResources<P>>) ==> args.0.state == UNUSED) &&
            forall |au:RequestResources<P>| args.1@ == Some(au) ==>
                ((forall |oldv:u64, p:P| Pred::inv(c, (oldv, p)) ==> #[trigger] au.requires(oldv, p)) &&
                 (forall |oldv:u64, p:P, p_prime:P| #[trigger] au.ensures(oldv, p, (), p_prime) ==>
                  Pred::inv(c, (args.0.val, p_prime)))
                 )
        }
    }

    impl<C, P, Pred: InvariantPredicate<C, (u64, P)>> Register<C, P, Pred> {
        spec fn constant(self) -> C;

        spec fn inv(self) -> bool {
            self.val.get_pred() == gen_val_pred::<C,P,Pred>(self.constant()) &&
            self.plist.get_pred() == gen_plist_pred::<C,P,Pred>(self.constant())
        }

        // background thread that executes operations requested by other threads.
        fn combiner(&self)
            requires self.inv()
        {
            loop
                invariant self.inv()
            {
                let (mut req, Tracked(res)) = self.plist.lock();
                if req.state == ACTIVE {
                    let (oldval, Tracked(p)) = self.val.lock();
                    // fire fupd
                    proof {
                        match res {
                            None => {
                                assert(false);
                            }
                            Some(au) => {
                                // really fire the fupd
                                assert(Pred::inv(self.constant(), (oldval, p)));
                                assert(au.requires(oldval, p));
                                p = (*au).call_once(oldval, p).1.get();
                            }
                        }
                    }
                    self.val.unlock((req.val, Tracked(p)));
                }
                req.state = UNUSED;
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
        fn async_write
            <Au:AtomicUpdate<u64, P, (), P>>
            (&self, v:u64, Tracked(au):Tracked<Au>)
            requires self.inv(),
            (forall |oldv:u64, p:P| Pred::inv(self.constant(), (oldv, p)) ==> #[trigger] au.requires(oldv, p)),
            (forall |oldv:u64, p:P, p_prime:P| #[trigger] au.ensures(oldv, p, (), p_prime) ==>
             Pred::inv(self.constant(), (v, p_prime))),
        {
            let mut req:WriteRequest;
            let tracked mut res;
            // wait for publication list to have an unused slot
            loop {
                let inner = self.plist.lock();
                req = inner.0;
                proof { res = inner.1.get(); }

                if req.state == UNUSED {
                    break
                }
                self.plist.unlock((req, Tracked(res)));
            }

            // send request
            req.state = ACTIVE;
            req.val = v;
            self.plist.unlock((req, Tracked(Some(_Dyn_AtomicUpdate::box_from(au)))));

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
