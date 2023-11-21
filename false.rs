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

    // □(At ={∅}=∗ Rt)
    pub trait PersistentAtomicUpdate<Ag, At, Rg, Rt> {
        proof fn call(tracked &self, ag:Ag, tracked at:At) -> (tracked r:(Ghost<Rg>, Tracked<Rt>));
            // opens_invariants any;
    }

    // XXX: this is manually written model for `dyn AtomicUpdate...`
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
        #[verifier(external_body)]
        proof fn box_from<T:PersistentAtomicUpdate<Ag,At,Rg,Rt>>(t:T) -> (tracked ret:Box<Self>)
        {
            unimplemented!();
        }
    }

    impl<Ag,At,Rg,Rt> PersistentAtomicUpdate<Ag,At,Rg,Rt> for _Dyn_PersistentAtomicUpdate<Ag,At,Rg,Rt> {
        #[verifier(external_body)]
        proof fn call(tracked &self, ag:Ag, tracked at:At) -> (tracked r:(Ghost<Rg>, Tracked<Rt>)) where Self: std::marker::Sized
        {
            unimplemented!();
        }
    }

    // XXX: end of model for `dyn AtomicUpdate`

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

    struct TruePredicate {}
    impl<C,V> InvariantPredicate<C, V> for TruePredicate {
        open spec fn inv(c: C, v: V) -> bool {
            true
        }
    }

    // TODO: put gname as one of the consts and write predicate about it
    type Inv = AtomicInvariant<(), Or<GhostToken, B>, TruePredicate>;

    // TODO: wrap this in a LocalInvariant to maintain gname property
    tracked struct BFupd {
        tracked wit: GhostWitness,
        tracked i:&'static Inv,
    }

    impl PersistentAtomicUpdate<(), (), (), False> for BFupd {
        proof fn call(tracked &self, ag:(), tracked at:()) ->
            (tracked r:(Ghost<()>, Tracked<False>))
            // FIXME: want to be able to open invariant here
        {
            let tracked mut b:Arc<Box<_Dyn_PersistentAtomicUpdate<(),(),(),False>>>;

            open_atomic_invariant!(&self.i => r =>{
                match r {
                    Or::Left(tok) => {
                        assume(tok.gname() == self.wit.gname());
                        token_witness_false(&tok, &self.wit);
                        r = Or::Left(tok);
                        b = false_to_anything();
                    }
                    Or::Right(b_in) => {
                        b = b_in.clone();
                        r = Or::Right(b_in);
                    }
                }
            });

            let tracked r:(Ghost<()>, Tracked<False>) = (**b).call((), ());

            return (Ghost(()), r.1);
            // return (Ghost(()), Tracked(b.call((), ())));
        }
    }

    proof fn prove_false() -> (tracked r:False)
        opens_invariants any
    {
        let tracked tok = token_new();
        let tracked i:Inv = AtomicInvariant::new((), Or::Left(tok), 37);
        // TODO: turn this into a shared reference

        let tracked mut b;
        open_atomic_invariant!(&i => r =>{
            match r {
                Or::Left(tok) => {
                    let tracked witness = token_freeze(tok);

                    let bf = BFupd{
                        wit: witness,
                        i: &i,
                    };
                    b = Arc::new(_Dyn_PersistentAtomicUpdate::box_from(bf));
                    r = Or::Right(b.clone());
                }
                Or::Right(b_in) => {
                    b = b_in.clone();
                    r = Or::Right(b_in);
                }
            }
        });

        let tracked f = (**b).call((), ()).1;
        return f.get();
    }

    fn main() {}
}
