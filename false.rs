#![feature(never_type)]
use vstd::{prelude::*, invariant::*};

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
        proof fn call(tracked &self, ag:Ag, at:At) -> (r:(Ghost<Rg>, Tracked<Rt>));
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
            // XXX: how does this fit into a model for `dyn T`?
            ensures
                (forall |ag, at| #[trigger] ret.requires(ag,at) == t.requires(ag,at)),
                (forall |ag, at, rg, rt| #[trigger] ret.ensures(ag,at,rg,rt) == t.ensures(ag,at,rg,rt))
        {
            unimplemented!();
        }
    }

    impl<Ag,At,Rg,Rt> PersistentAtomicUpdate<Ag,At,Rg,Rt> for _Dyn_PersistentAtomicUpdate<Ag,At,Rg,Rt> {
        #[verifier(external_body)]
        proof fn call_once(tracked self, ag:Ag, tracked at:At) -> (tracked r:(Ghost<Rg>, Tracked<Rt>)) where Self: std::marker::Sized
        {
            unimplemented!();
        }
    }

    // XXX: end of model for `dyn AtomicUpdate`

    enum Or<A,B> {
        Left(A),
        Right(B),
    }

    // type B<F:PersistentAtomicUpdate> = F;

    // Definition B : PROP := □ fupd M1 False.
    type B = Box<dyn PersistentAtomicUpdate<(), (), (), !>>;

    // Definition P (γ : gname) : PROP := start γ ∨ B.
    // Definition I (i : name) (γ : gname) : PROP := inv i (start γ ∨ B).

    struct TruePredicate {}
    impl<C,V> InvariantPredicate<C, V> for TruePredicate {
        open spec fn inv(c: C, v: V) -> bool {
            true
        }
    }

    type Inv  = AtomicInvariant<(), Or<GhostToken, B>, TruePredicate>;

    proof fn prove_false() {
        let tok = token_new();
        // FIXME: error: The verifier does not yet support the following Rust feature: dynamic types

        let a:Inv = AtomicInvariant::new((), Or::Left(tok), 37);
    }

    fn main() {}
}
