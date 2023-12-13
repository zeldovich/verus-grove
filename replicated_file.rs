use vstd::{prelude::*,invariant::*,thread::*};

verus! {
    // XXX: model for fupds
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

    #[verifier(external_body)]
    pub struct CrashBorrow<P,Q>;

    #[verifier(external_body)]
    pub struct FilePointsTo;

    tracked pub struct WritePre<R,R',Qc',S> {
        tracked c: CrashBorrow<R,Qc'>
    }

    fn file_write(data:u64, ) {
    }

    #[verifier(external_body)]
    fn main() {
    }
} // verus!
