#![feature(never_type)]
use vstd::{prelude::*, invariant::*};
use std::sync::Arc;

verus! {
    #[verifier(external_body)]
    pub struct GhostToken;

    #[verifier(external_body)]
    pub struct GhostWitness;

    impl GhostToken {
        pub spec fn gname(&self) -> nat;
    }

    impl GhostWitness {
        pub spec fn gname(&self) -> nat;
    }

    #[verifier(external_body)]
    proof fn token_new() -> (tracked r:GhostToken)
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    proof fn token_exlcusive(tracked a:&GhostToken, tracked b:&GhostToken)
        requires a.gname() == b.gname()
        ensures false
    {
    }

    #[verifier(external_body)]
    proof fn token_freeze(tracked a:GhostToken) -> (tracked b:GhostWitness)
        ensures a.gname() == b.gname()
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    proof fn token_witness_false(tracked a:&GhostToken, tracked b:&GhostWitness)
        requires a.gname() == b.gname()
        ensures false
    {
    }

    #[verifier(external_body)]
    proof fn witness_clone(tracked a:&GhostWitness) -> (tracked b:GhostWitness)
        ensures a.gname() == b.gname()
    {
        unimplemented!();
    }

    enum Or<A,B> {
        Left(A),
        Right(B),
    }

    // XXX: verus doesn't seem to support ! type. Can introduce mathematical
    // predicates to fupds if to get rid of this `external_body`.
    #[verifier(external_body)]
    pub struct False {
        pub x:!
    }

    #[verifier(external_body)]
    proof fn false_to_anything<A>() -> (tracked r:A)
        requires false
    {
        unimplemented!();
    }

    // Definition B : PROP := □ fupd M1 False.
    type B = Arc<Box<_Dyn_PersistentAtomicUpdate<(), (), (), False>>>;

    // Definition P (γ : gname) : PROP := start γ ∨ B.
    // Definition I (i : name) (γ : gname) : PROP := inv i (start γ ∨ B).

    struct MyInvPredicate {}
    impl InvariantPredicate<nat, Or<GhostToken, B>> for MyInvPredicate {
        closed spec fn inv(gname: nat, v: Or<GhostToken, B>) -> bool {
            match v {
                Or::Left(tok) => tok.gname() == gname,
                Or::Right(b) => (**b).wf()
            }
        }
    }

    type Inv = AtomicInvariant<nat, Or<GhostToken, B>, MyInvPredicate>;

    // □(At ={⊤}=∗ Rt)
    // 
    // XXX: this is a manually written model for `dyn AtomicUpdate...` without
    // any trait backing. This is because Verus doesn't currently support proof
    // fns with non-empty masks in traits.
    #[verifier(external_body)]
    #[verifier::reject_recursive_types(Ag)]
    #[verifier::reject_recursive_types(At)]
    #[verifier::reject_recursive_types(Rg)]
    #[verifier::reject_recursive_types(Rt)]
    #[allow(non_camel_case_types)]
    struct _Dyn_PersistentAtomicUpdate<Ag, At, Rg, Rt> {
        _unused1: std::marker::PhantomData<Ag>,
        _unused2: std::marker::PhantomData<At>,
        _unused3: std::marker::PhantomData<Rg>,
        _unused4: std::marker::PhantomData<Rt>,
    }

    impl<Ag,At,Rg,Rt> _Dyn_PersistentAtomicUpdate<Ag,At,Rg,Rt> {
        // This is so that BFupd can maintain mathematical stuff
        spec fn wf(self) -> bool;

        #[verifier(external_body)]
        proof fn call(tracked &self, ag:Ag, tracked at:At) -> (tracked r:(Ghost<Rg>, Tracked<Rt>))
            requires self.wf()
            opens_invariants any
        {
            unimplemented!();
        }
    }

    // Doing this complicated thing just to say that `wit.gname() == i.constant()`
    tracked struct BFupdInner {
        tracked wit: GhostWitness,
        tracked i: Arc<Inv>,
    }
    struct BFupdPredicate {}
    impl InvariantPredicate<(), BFupdInner> for BFupdPredicate {
        closed spec fn inv(c: (), v: BFupdInner) -> bool {
            v.wit.gname() == v.i.constant() &&
            v.i.namespace() == 37
        }
    }
    tracked struct BFupd {
        tracked res:LocalInvariant<(), BFupdInner, BFupdPredicate>
    }

    impl BFupd {
        spec fn wf(self) -> bool {
            self.res.namespace() == 38
        }

        proof fn call(tracked &self, ag:(), tracked at:()) -> (tracked r:(Ghost<()>, Tracked<False>))
            requires self.wf()
            opens_invariants any
        {
            let tracked mut b:Arc<Box<_Dyn_PersistentAtomicUpdate<(),(),(),False>>>;

            open_local_invariant!(&self.res => bfi =>{
                open_atomic_invariant!(&bfi.i => r =>{
                    match r {
                        Or::Left(tok) => {
                            token_witness_false(&tok, &bfi.wit);
                            r = Or::Left(tok);
                            b = false_to_anything();
                        }
                        Or::Right(b_in) => {
                            b = b_in.clone();
                            r = Or::Right(b_in);
                        }
                    }
                });
            });

            let tracked r:(Ghost<()>, Tracked<False>) = (**b).call((), ());

            return r;
        }
    }

    // XXX: This is part of the model because BFupd implements the
    // `call` function with the exact same types/spec as _Dyn_PersistentAtomicUpdate's.
    // Ideally, we'd have a Trait that contains all the functions available on a `_Dyn_PersAu`.
    // Then, there would be a function that takes any type `T:PersAu` and gives
    // a `DynPersAu` (i.e. that would be going from T → dyn Trait when T
    // implements Trait).
    // However, Verus currently doesn't support putting non-trivial masks on
    // proof fns in traits, which is important for this proof. Hence, this hack
    // for now.
    #[verifier(external_body)]
    proof fn box_from(tracked b:BFupd) -> (tracked r: Box<_Dyn_PersistentAtomicUpdate<(), (), (), False>>)
        ensures b.wf() == (*r).wf()
    {
        unimplemented!();
    }

    proof fn prove_false() -> (tracked r:False)
        opens_invariants any
    {
        let tracked tok = token_new();
        let tracked i:Arc<Inv> = Arc::new(AtomicInvariant::new(tok.gname(), Or::Left(tok), 37));
        let tracked i2 = i.clone();

        let tracked mut b;
        open_atomic_invariant!(&(*i) => r =>{
            match r {
                Or::Left(tok) => {
                    let tracked witness = token_freeze(tok);

                    let tracked bfi = BFupdInner{
                        wit: witness,
                        i: i2,
                    };
                    let tracked bf = LocalInvariant::new((), bfi, 38);
                    b = Arc::new(box_from(BFupd{res:bf}));
                    r = Or::Right(b.clone());
                }
                Or::Right(b_in) => {
                    b = b_in.clone();
                    r = Or::Right(b_in);
                }
            }
        });

        return (**b).call((), ()).1.get();
    }

    fn main() {}
}
