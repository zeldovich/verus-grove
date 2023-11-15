use vstd::{prelude::*, invariant::*};
mod kv;
use kv::lmap;

verus! {

    pub struct KvState<P, C, Pred> {
        m: lmap::LMap<u64, u64>,
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
    impl<P, C, Pred:InvariantPredicate<(P,Map<u64,u64>), C,>> KvState<P,C,Pred> {
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
            requires Pred::inv((args.1@, args.0@), c)
            ensures Pred::inv((ret, args.0@.insert(2u64,37u64)), c)
            opens_invariants any
        {
            todo!();
        }

        // requires [ ∀ σ, P σ ==∗ P (σ.insert(k,v)) ∗ Φ ]
        // ensures  Φ
        #[verifier(external_body)]
        pub fn put_hocap<Phi, F: FnOnce(Tracked<P>, Ghost<Map<u64,u64>>) -> (Tracked<P>, Phi) >
            (&mut self, k:u64, v:u64, au:Tracked<F>) -> (ret:Phi)

            requires
            old(self).inv(),
            // XXX: can't do it this way
            // forall |sigma, res| Pred::inv((res, sigma), old(self).constant()) ==> au@.requires((Tracked(res), Ghost(sigma))),
            forall |sigma:Ghost<_>, res:Tracked<_>, res_prime:Tracked<_>, phi|
            (#[trigger] Pred::inv((res@, sigma@), old(self).constant()) ==> au@.requires((res, sigma))) &&
            (#[trigger] au@.ensures((res, sigma), (res_prime, phi)) ==> Pred::inv((res_prime@, sigma@.insert(k,v)), old(self).constant())),

            ensures
            self.inv(),
            self.constant() == old(self).constant(),
        {
            unimplemented!();
        }

        // TODO: need to have a FnSpec or Trait predicate for Φ as well
        // requires [ ∀ σ, P σ ==∗ P (σ.insert(k,v)) ∗ Φ(lookup(σ,k) == exp) ]
        // ensures  Φ
        #[verifier(external_body)]
        pub fn cput_hocap<Phi, F: FnOnce(Tracked<P>, Ghost<Map<u64,u64>>) -> (Tracked<P>, Phi) >
            (&mut self, k:u64, exp:u64, v:u64, au:Tracked<F>) -> (ret:(bool, Phi))

            requires
            old(self).inv(),
            forall |sigma:Ghost<_>, res:Tracked<_>, res_prime:Tracked<_>, phi|
            (#[trigger] Pred::inv((res@, sigma@), old(self).constant()) ==> au@.requires((res, sigma))) &&
            (#[trigger] au@.ensures((res, sigma), (res_prime, phi)) ==> Pred::inv((res_prime@, sigma@.insert(k,v)), old(self).constant())),

            ensures
            self.inv(),
            self.constant() == old(self).constant(),
        {
            unimplemented!();
        }

        // requires (P ∅)
        #[verifier(external_body)]
        pub fn new(res:P, c:C) -> (kv:KvState<P,C,Pred>)
            requires Pred::inv((res, Map::<u64,u64>::empty()), c),

            ensures kv.constant() == c,
        {
            unimplemented!();
        }
    }

    fn main() {}
} // verus!
