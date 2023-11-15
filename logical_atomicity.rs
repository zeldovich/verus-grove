use vstd::{prelude::*, invariant::*};

verus! {

    pub struct KvClient<P, C, Pred> {
        _p:std::marker::PhantomData<P>,
        _c:std::marker::PhantomData<C>,
        _pred:std::marker::PhantomData<Pred>,
    }

    spec fn lookup(m:Map<u64,u64>, k:u64) -> u64 {
        if m.contains_key(k) {
            m[k]
        }
        else {
            0u64
        }
    }

    spec fn gauge_eq(m1:Map<u64,u64>, m2:Map<u64,u64>) -> bool {
        forall|k:u64| lookup(m1, k) == lookup(m2, k)
    }

    // Q: put traits only in `impl` or also on struct?
    impl<P, C, Pred:InvariantPredicate<C, (P,Map<u64,u64>)>> KvClient<P,C,Pred> {
        pub spec fn constant(self) -> C;

        pub closed spec fn inv(self) -> bool {
            true // gauge_eq(self.m@, self.ghostKvs@.kvs)
        }

        // #[verifier(external_body)]
        // proof fn example_fupd(sigma:Map<u64,u64>, tracked res:P) -> (ret:P)
        //     requires Pred::inv((res, sigma), ())
        //     ensures Pred::inv((res, sigma.insert(2u64,37u64)), ())
        //     opens_invariants any
        // {
        //     todo!();
        // }

        #[verifier(external_body)]
        proof fn example_fupd2(args:(Ghost<Map<u64,u64>>, Tracked<P>), c:C) -> (ret:P)
            requires Pred::inv(c, (args.1@, args.0@))
            ensures Pred::inv(c, (ret, args.0@.insert(2u64,37u64)))
            opens_invariants any
        {
            todo!();
        }

        // TODO: predicate-wrap Phi?
        // requires [ ∀ σ, P σ ==∗ P (σ.insert(k,v)) ∗ Φ ]
        // ensures  Φ
        #[verifier(external_body)]
        pub fn put_hocap<Phi, F: FnOnce(Tracked<P>, Ghost<Map<u64,u64>>) -> (Tracked<P>, Phi) >
            (&self, k:u64, v:u64, au:Tracked<F>) -> (ret:Phi)

            requires
            self.inv(),
            // XXX: can't do it this way
            // forall |sigma, res| Pred::inv((res, sigma), old(self).constant()) ==> au@.requires((Tracked(res), Ghost(sigma))),
            forall |sigma:Ghost<_>, res:Tracked<_>, res_prime:Tracked<_>, phi|
            (#[trigger] Pred::inv(self.constant(), (res@, sigma@)) ==> au@.requires((res, sigma))) &&
            (#[trigger] au@.ensures((res, sigma), (res_prime, phi)) ==> Pred::inv(self.constant(), (res_prime@, sigma@.insert(k,v)))),
        {
            unimplemented!();
        }

        // TODO: need to have a FnSpec or Trait predicate for Φ as well
        // requires [ ∀ σ, P σ ==∗ P σ' ∗ Φ(lookup(σ,k) == exp) ]
        // ensures  Φ
        #[verifier(external_body)]
        pub fn cput_hocap<PhiRes, F: FnOnce(Tracked<P>, Ghost<Map<u64,u64>>) -> Tracked<(P, PhiRes)>>
            (&self, k:u64, exp:u64, v:u64, au:F,
             phiPred: Ghost<FnSpec(bool, PhiRes) ->  bool>, // XXX: curry?
            ) -> (ret:(bool, Tracked<PhiRes>))

            requires
            self.inv(),
            forall |sigma:Ghost<_>, res:Tracked<_>, au_ret:Tracked<_>|
            (#[trigger] Pred::inv(self.constant(), (res@, sigma@)) ==> au.requires((res, sigma))) &&
            (#[trigger] au.ensures((res, sigma), au_ret)) ==> Pred::inv(self.constant(), (au_ret@.0, sigma@.insert(k,v))),

            ensures phiPred@(ret.0, ret.1@)
        {
            unimplemented!();
        }

        // requires (P ∅)
        #[verifier(external_body)]
        pub fn new(res:P, c:C) -> (kv:KvClient<P,C,Pred>)
            requires Pred::inv(c, (res, Map::<u64,u64>::empty())),

            ensures kv.constant() == c,
        {
            unimplemented!();
        }
    }

    enum Or<A,B> {
        Left(A),
        Right(B),
    }

    type LockInvRes<R> = Or<R,()>;
    struct LockInvConsts {}
    struct LockInvPredicate{}

    // InvariantPredicate<(P,Map<u64,u64>)
    impl<R> InvariantPredicate<LockInvConsts, (LockInvRes<R>, Map<u64,u64>)> for LockInvPredicate {
        closed spec fn inv(c: LockInvConsts, r: (LockInvRes<R>, Map<u64,u64>)) -> bool {
            // if unlocked, the invariant must have the resource
            if lookup(r.1, 37) == 0 {
                match r.0 {
                    Or::Left(_) => true,
                    Or::Right(_) => false,
                }
            } else {
                true
            }
        }
    }

    type PhiRes<R> = Or<R,()>;

    // phiPred: (FnSpec(bool, PhiRes) ->  bool)
    spec fn phi_pred<R>() -> FnSpec(bool, PhiRes<R>) -> bool {
        |ret:bool, res:PhiRes<R>| {
            true
        }
    }

    fn trylock_cput_au<R>(res:Tracked<LockInvRes<R>>, sigma:Ghost<Map<u64,u64>>) ->
        (x:Tracked<(LockInvRes<R>, PhiRes<R>)>)
    {
        let tracked phiRes;
        proof {
            match res.get() {
                Or::Left(r) => {
                    // ret = Tracked(Or::Right(()));, Or::Left(r);
                    phiRes = Or::Left(r);
                }
                Or::Right(()) => {
                    // ret = (Tracked(Or::Right(())), Or::Right(()));
                    phiRes = Or::Right(());
                }
            }
        }
        return Tracked((Or::Right(()), phiRes));
    }

    #[verifier(external_body)]
    proof fn false_to_anything<A>() -> (tracked r:A)
        requires false
    {
        unimplemented!();
    }

    fn spinlock_acquire<R>(kv:&KvClient<LockInvRes<R>, LockInvConsts, LockInvPredicate>)
        -> Tracked<R>
    {
       loop {
           let au = |res:Tracked<_>, sigma| -> Tracked<_>
               requires false
               // FIXME: requires/ensures
           {
               trylock_cput_au(res, sigma)
           };

           // assert(forall |sigma:Ghost<_>, res:Tracked<_>| (#[trigger] LockInvPredicate::inv(kv.constant(), (res@, sigma@)) ==> au.requires((res, sigma))));
           let ret = kv.cput_hocap(37, 0, 1, au, Ghost(phi_pred()));
           // assert(forall |sigma:Ghost<_>, res:Tracked<_>| (#[trigger] LockInvPredicate::inv(kv.constant(), (res@, sigma@)) ==> au.requires((res, sigma))));

           if ret.0 == true {
               let tracked r;
               proof {
                   match ret.1.get() {
                       Or::Left(r2) => {
                           r = r2;
                       }
                       Or::Right(()) => {
                           assert(false);
                           r = false_to_anything();
                      }
                   }
               }
               return Tracked(r)
           }
       }
    }

    fn main() {}
} // verus!
