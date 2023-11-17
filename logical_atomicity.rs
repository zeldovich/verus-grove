use vstd::{prelude::*, invariant::*};

verus! {
    pub struct KvClient<P, C, Pred> {
        _p:std::marker::PhantomData<P>,
        _c:std::marker::PhantomData<C>,
        _pred:std::marker::PhantomData<Pred>,
    }

    pub open spec fn lookup(m:Map<u64,u64>, k:u64) -> u64 {
        if m.contains_key(k) {
            m[k]
        }
        else {
            0u64
        }
    }

    // FnProof(x) -> Y

    pub trait AtomicUpdate<Ag, At, Rg, Rt> {
        spec fn requires(&self, ag:Ag, at:At) -> bool;
        spec fn ensures(&self, ag:Ag, at:At, rg:Rg, rt:Rt) -> bool;
        proof fn call_once(tracked self, ag:Ag, tracked at:At) -> (tracked r:(Ghost<Rg>, Tracked<Rt>)) where Self: std::marker::Sized
            requires self.requires(ag, at)
            ensures self.ensures(ag, at, r.0@, r.1@);
    }

    // Q: put traits only in `impl` or also on struct?
    impl<P, C, Pred:InvariantPredicate<C, (P,Map<u64,u64>)>> KvClient<P,C,Pred> {
        pub spec fn constant(self) -> C;

        pub closed spec fn inv(self) -> bool {
            true // gauge_eq(self.m@, self.ghostKvs@.kvs)
        }

        // XXX: no need to predicate-wrap Phi here for the spinlock use-case.
        // requires [ ∀ σ, P σ ==∗ P (σ.insert(k,v)) ∗ Φ ]
        // ensures  Φ
        #[verifier(external_body)]
        pub fn put_hocap<Phi, Au: AtomicUpdate<Map<u64,u64>, P, (), (P, Phi)>>
            (&self, k:u64, v:u64, Tracked(au):Tracked<Au>) -> (ret:Tracked<Phi>)

            requires
            self.inv(),
            // XXX: can't do it this way
            // forall |sigma, res| Pred::inv((res, sigma), old(self).constant()) ==> au@.requires((Tracked(res), Ghost(sigma))),
            forall |sigma, res, res_prime|
            (#[trigger] Pred::inv(self.constant(), (res, sigma)) ==> au.requires(sigma, res)) &&
            (#[trigger] au.ensures(sigma, res, (), res_prime) ==> Pred::inv(self.constant(), (res_prime.0, sigma.insert(k,v)))),
        {
            unimplemented!();
        }

        // requires [ ∀ σ, P σ ==∗ P σ' ∗ Φ(lookup(σ,k)) ]
        // ensures  Φ
        #[verifier(external_body)]
        pub fn get_and_put_hocap<PhiRes, // F: FnOnce(Tracked<P>, Ghost<Map<u64,u64>>) -> Tracked<(P, PhiRes)>>
                                 Au: AtomicUpdate<Map<u64,u64>, P, (), (P, PhiRes)>>
            (&self, k:u64, v:u64, Tracked(au):Tracked<Au>,
             phiPred: Ghost<FnSpec(u64, PhiRes) ->  bool>, // XXX: curry?
            ) -> (ret:(u64, Tracked<PhiRes>))

            requires
            self.inv(),
            forall |sigma, res, au_ret|
            (#[trigger] Pred::inv(self.constant(), (res, sigma)) ==> au.requires(sigma, res)) &&
            (#[trigger] au.ensures(sigma, res, (), au_ret) ==>
                 Pred::inv(self.constant(), (au_ret.0, sigma.insert(k,v))) &&
                 phiPred@(lookup(sigma, k), au_ret.1)
            )
            ,

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
    spec fn phi_pred<R>() -> FnSpec(u64, PhiRes<R>) -> bool {
        |ret:u64, res:PhiRes<R>| {
            match res {
                Or::Left(_) => true,
                Or::Right(_) => ret != 0,
            }
        }
    }

    #[verifier(external_body)]
    proof fn false_to_anything<A>() -> (tracked r:A)
        requires false
    {
        unimplemented!();
    }

    pub struct AcquireAu {
        ghost c: LockInvConsts,
    }

    impl<R> AtomicUpdate<Map<u64,u64>, LockInvRes<R>, (), (LockInvRes<R>, PhiRes<R>)> for AcquireAu {
        closed spec fn requires(&self, sigma:Map<u64,u64>, res:LockInvRes<R>) -> bool {
            LockInvPredicate::inv(self.c, (res, sigma))
        }

        closed spec fn ensures(&self, sigma:Map<u64,u64>, res:LockInvRes<R>, _unused:(), ret:(LockInvRes<R>, PhiRes<R>)) -> bool {
            LockInvPredicate::inv(self.c, (ret.0, sigma.insert(37,1))) &&
            phi_pred::<R>()(lookup(sigma, 37), ret.1)
        }

        proof fn call_once(tracked self, sigma:Map<u64,u64>, tracked res:LockInvRes<R>) ->
            (tracked r:(Ghost<()>, Tracked<(LockInvRes<R>, PhiRes<R>)>))
        {
            let tracked phiRes;
            match res {
                Or::Left(r) => {
                    phiRes = Or::Left(r);
                }
                Or::Right(()) => {
                    phiRes = Or::Right(());
                }
            }
            return (Ghost(()), Tracked((Or::Right(()), phiRes)));
        }
    }

    fn spinlock_acquire<R>(kv:&KvClient<LockInvRes<R>, LockInvConsts, LockInvPredicate>)
        -> Tracked<R>
    {
       loop {
           let ghost c = kv.constant();

           let tracked au : AcquireAu;
           proof {
               au = AcquireAu{c: kv.constant()};
           }
           let ret = kv.get_and_put_hocap::<_, AcquireAu>(37, 1, Tracked(au), Ghost(phi_pred()));

           if ret.0 == 0 {
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

    pub struct ReleaseAu<R> {
        ghost c: LockInvConsts,
        tracked r: R,
    }

    impl<R> AtomicUpdate<Map<u64,u64>, LockInvRes<R>, (), (LockInvRes<R>, ())> for ReleaseAu<R> {
        closed spec fn requires(&self, sigma:Map<u64,u64>, res:LockInvRes<R>) -> bool {
            LockInvPredicate::inv(self.c, (res, sigma))
        }

        closed spec fn ensures(&self, sigma:Map<u64,u64>, res:LockInvRes<R>, _unused:(), ret:(LockInvRes<R>, ())) -> bool {
            LockInvPredicate::inv(self.c, (ret.0, sigma.insert(37,0)))
        }

        proof fn call_once(tracked self, sigma:Map<u64,u64>, tracked res:LockInvRes<R>) ->
            (tracked r:(Ghost<()>, Tracked<(LockInvRes<R>, ())>))
        {
            return (Ghost(()), Tracked((Or::Left(self.r), ())));
        }
    }

    fn spinlock_release<R>(kv:&KvClient<LockInvRes<R>, LockInvConsts, LockInvPredicate>, r:Tracked<R>)
    {
        let ghost c = kv.constant();
        let tracked au = ReleaseAu{c:kv.constant(), r:r.get()};

        kv.put_hocap::<_,ReleaseAu<R>>(37, 0, Tracked(au));
        // FIXME: type inference picks the wrong type for `put_hocap`'s `Au`.
        // kv.put_hocap(37, 0, Tracked(au)); 
    }

    fn main() {}
} // verus!
