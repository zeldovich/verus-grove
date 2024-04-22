#![verifier::loop_isolation(false)]
#![allow(non_camel_case_types)]
use vstd::{prelude::*};
use std::vec::Vec;
mod lock;

verus! {

const NUM_REPLICAS : u64 = 37;
type StateType = u64;
type Error = u64;
const ENone : u64 = 0u64;
const EEpochStale : u64 = 1u64;
const ENotLeader : u64 = 2u64;

////////////////////////////////////////////////////////////////////////////////
// Acceptor

struct AcceptorState {
    epoch : u64,
    accepted_epoch : u64,
    next_index : u64,
    state : StateType,
}

type AcceptorResource = u64;

pub struct Acceptor {
    mu: lock::Lock<(AcceptorState, Tracked<AcceptorResource>)>,
}

#[derive(Clone, Copy)]
struct AcceptorApplyArgs {
    epoch:u64,
    next_index:u64,
    state:StateType,
}

type AcceptorApplyReply = u64;

impl Acceptor {
    spec fn inv(self) -> bool {
        forall |s| #[trigger] self.mu.get_pred()(s) <==> true // server_inv(s.0, s.1@)
    }

    fn apply(&self, args:AcceptorApplyArgs) -> (ret:AcceptorApplyReply)
        requires self.inv()
    {
        let (mut s, mut res) = self.mu.lock();
        let mut reply;

        if s.epoch <= args.epoch {
            if s.accepted_epoch == args.epoch {
                if s.next_index < args.next_index {
                    s.next_index = args.next_index;
                    s.state = args.state;
                    reply = ENone;
                } else { // args.next_index < s.next_index
                    reply = ENone;
                }
            } else { // s.accepted_epoch < args.epoch, because s.accepted_epoch <= s.epoch <= args.epoch
                s.accepted_epoch = args.epoch;
                s.epoch = args.epoch;
                s.state = args.state;
                s.next_index = args.next_index;
                reply = ENone;
            }
        } else {
            reply = EEpochStale;
        }

        self.mu.unlock((s, res));
        return 0;
    }

}

////////////////////////////////////////////////////////////////////////////////
// Proposer

struct ProposerState {
    epoch : u64,
    next_index : u64,
    state : StateType,

    is_leader : bool,
    clerks : Vec<&'static Acceptor>,
}

type ProposerResource = u64;

pub struct Proposer {
    mu: lock::Lock<(ProposerState, Tracked<ProposerResource>)>,
}

spec fn proposer_inv(s:ProposerState, res:ProposerResource) -> bool {
    &&& s.clerks@.len() == NUM_REPLICAS
    &&& forall |j| 0 <= j < s.clerks.len() ==> #[trigger] s.clerks[j].inv()
}

impl Proposer {
    spec fn inv(self) -> bool {
        forall |s| #[trigger] self.mu.get_pred()(s) <==> proposer_inv(s.0, s.1@)
    }

    // TODO: take as input a "step" function
    fn try_apply(&self) -> Error
        requires self.inv()
    {
        let (mut s, mut res) = self.mu.lock();
        if !s.is_leader {
            self.mu.unlock((s, res));
            return ENotLeader;
        }

        let mut num_successes = 0u64;
        let args = AcceptorApplyArgs{
            epoch: s.epoch,
            next_index: s.next_index,
            state: s.state,
        };

        let mut i : usize = 0;

        while i < NUM_REPLICAS as usize
            invariant
              0 <= i <= NUM_REPLICAS,
              0 <= num_successes <= i,
        {
            let reply = s.clerks[i].apply(args);
            if reply == ENone {
                num_successes += 1;
            }
            i += 1;
        }

        if 2*num_successes > NUM_REPLICAS {
            return ENone
        }
        return EEpochStale
    }
}

////////////////////////////////////////////////////////////////////////////////
// General definitions

type True = ();
type Pure = ();

/// P ∗ Q
type ⟦∗⟧<⟦P⟧,⟦Q⟧> = (⟦P⟧, ⟦Q⟧);
spec fn ⟨∗⟩<⟦P⟧,⟦Q⟧>(⟨P⟩:spec_fn(⟦P⟧) -> bool, ⟨Q⟩:spec_fn(⟦Q⟧) -> bool)
    -> spec_fn(⟦∗⟧<⟦P⟧,⟦Q⟧>) -> bool {
    |res:⟦∗⟧<_,_>| {
        &&& ⟨P⟩(res.0)
        &&& ⟨Q⟩(res.1)
    }
}


/// P ∨ Q
enum ⟦or⟧<A,B> {Left(A), Right(B)}
spec fn ⟨or⟩<⟦P⟧,⟦Q⟧>(⟨P⟩:spec_fn(⟦P⟧) -> bool, ⟨Q⟩:spec_fn(⟦Q⟧) -> bool)
    -> spec_fn(⟦or⟧<⟦P⟧,⟦Q⟧>) -> bool {
    |res:⟦or⟧<⟦P⟧,⟦Q⟧>| {
        match res {
            ⟦or⟧::Left(res) => ⟨P⟩(res),
            ⟦or⟧::Right(res) => ⟨Q⟩(res),
        }
    }
}


/// P -∗ Q
trait wand_tr<P, Q> {
    spec fn inv(&self) -> bool;
    spec fn pre(&self) -> spec_fn(x:P) -> bool;
    spec fn post(&self) -> spec_fn(x:Q) -> bool;

    proof fn instantiate(tracked self, tracked i:P) -> (tracked out:Q) where Self: std::marker::Sized
        requires
          self.inv(),
          self.pre()(i),
        ensures self.post()(out)
        opens_invariants none
        ;
}

/// model for dyn wand_tr
#[verifier(external_body)]
#[verifier::reject_recursive_types(⟦P⟧)]
#[verifier::reject_recursive_types(⟦Q⟧)]
struct ⟦-∗⟧<⟦P⟧,⟦Q⟧> {
    _phantom : std::marker::PhantomData<(⟦P⟧,⟦Q⟧)>,
}
impl<⟦P⟧, ⟦Q⟧> wand_tr<⟦P⟧, ⟦Q⟧> for ⟦-∗⟧<⟦P⟧, ⟦Q⟧> {
    spec fn inv(&self) -> bool;
    spec fn pre(&self) -> spec_fn(x:⟦P⟧) -> bool;
    spec fn post(&self) -> spec_fn(x:⟦Q⟧) -> bool;

    #[verifier(external_body)]
    proof fn instantiate(tracked self, tracked i:⟦P⟧) -> (tracked out:⟦Q⟧) {
        unimplemented!();
    }
}
impl<⟦P⟧, ⟦Q⟧> ⟦-∗⟧<⟦P⟧, ⟦Q⟧> {
    #[verifier(external_body)]
    proof fn from<T:wand_tr<⟦P⟧,⟦Q⟧>>(tracked x:T) -> (tracked r:Self)
        requires x.inv()
        ensures
        r.inv(),
        r.pre() == x.pre(),
        r.post() == x.post(),
    {
        unimplemented!()
    }
}
spec fn ⟨-∗⟩<⟦P⟧,⟦Q⟧>(⟨P⟩:spec_fn(⟦P⟧) -> bool, ⟨Q⟩:spec_fn(⟦Q⟧) -> bool)
    -> spec_fn(⟦-∗⟧<⟦P⟧,⟦Q⟧>) -> bool {
    |res:⟦-∗⟧<_,_>| {
        &&& res.pre() == ⟨P⟩
        &&& res.post() == ⟨Q⟩
        &&& res.inv()
    }
}



/// ∀ (x:X), A(x)   where A is a predicate.
trait forall_tr<X, ⟦A⟧> {
    spec fn inv(&self) -> bool;
    spec fn post(&self) -> spec_fn(x:X) -> spec_fn(out:⟦A⟧) -> bool;

    proof fn instantiate(tracked self, x:X) -> (tracked out:⟦A⟧) where Self: std::marker::Sized
        requires self.inv()
        ensures self.post()(x)(out)
    ;
}

/// model for dyn forall_tr
#[verifier(external_body)]
#[verifier::reject_recursive_types(X)]
#[verifier::reject_recursive_types(⟦A⟧)]
struct ⟦∀⟧<X,⟦A⟧> {
    _phantom : std::marker::PhantomData<(X,⟦A⟧)>,
}
impl<X,⟦A⟧> forall_tr<X,⟦A⟧> for ⟦∀⟧<X,⟦A⟧> {
    spec fn inv(&self) -> bool;
    spec fn post(&self) -> spec_fn(x:X) -> spec_fn(out:⟦A⟧) -> bool;

    #[verifier(external_body)]
    proof fn instantiate(tracked self, x:X) -> (tracked out:⟦A⟧) {
        unimplemented!();
    }
}
impl<X,⟦A⟧> ⟦∀⟧<X,⟦A⟧> {
    #[verifier(external_body)]
    proof fn from<T:forall_tr<X, ⟦A⟧>>(tracked t:T) -> (tracked r:Self)
        requires t.inv()
        ensures
          r.inv(),
          r.post() == t.post(),
    {
        unimplemented!()
    }
}
spec fn ⟨∀⟩<X,⟦A⟧>(⟨A⟩:spec_fn(x:X) -> spec_fn(out:⟦A⟧) -> bool)
    -> spec_fn(⟦∀⟧<X,⟦A⟧>) -> bool
{
    |res:⟦∀⟧<_,_>| {
        &&& res.post() == ⟨A⟩ 
        &&& res.inv()
    }
}

/// Trait capturing what must be provided to show ∃ (x:X), A(x)
trait exists_tr<X, ⟦A⟧> {
    spec fn post(&self) -> spec_fn(x:X) -> spec_fn(out:⟦A⟧) -> bool;

    proof fn destruct(tracked self) -> (tracked out:(Ghost<X>, ⟦A⟧)) where Self: std::marker::Sized
        ensures self.post()(out.0@)(out.1)
    ;
}

/// ∃ x, A(x); modeled as a dyn exists_tr.
#[verifier(external_body)]
#[verifier::reject_recursive_types(X)]
#[verifier::reject_recursive_types(⟦A⟧)]
struct ⟦∃⟧<X,⟦A⟧> {
    _phantom : std::marker::PhantomData<(X,⟦A⟧)>,
}
impl<X,⟦A⟧> exists_tr<X,⟦A⟧> for ⟦∃⟧<X,⟦A⟧> {
    spec fn post(&self) -> spec_fn(x:X) -> spec_fn(out:⟦A⟧) -> bool;

    #[verifier(external_body)]
    proof fn destruct(tracked self) -> (tracked out:(Ghost<X>, ⟦A⟧)) {
        unimplemented!();
    }
}
impl<X,⟦A⟧> ⟦∃⟧<X,⟦A⟧> {
    // This statement makes it so that when the returned value is ever asserted
    // to satisfy ⟨∃⟩, the forall will reduce it to something that must be true
    // about x and HA.
    #[verifier(external_body)]
    proof fn exists(x:X, tracked HA:⟦A⟧) -> (tracked r:Self)
      ensures
        forall |⟨A⟩:spec_fn(X) -> spec_fn(⟦A⟧) -> bool|
            ⟨A⟩(x)(HA) ==> #[trigger] ⟨∃⟩(⟨A⟩)(r)
    {
        unimplemented!();
    }
}
spec fn ⟨∃⟩<X,⟦A⟧>(⟨A⟩:spec_fn(x:X) -> spec_fn(out:⟦A⟧) -> bool)
    -> spec_fn(⟦∃⟧<X,⟦A⟧>) -> bool
{
    |res:⟦∃⟧<_,_>| {
        res.post() == ⟨A⟩
    }
}

trait Duplicable {
    proof fn dup(tracked &self) -> (tracked r:Self) where Self: std::marker::Sized
        ensures r == self;
}

/// □ P
trait □_tr<⟦P⟧> {
    // This is here so the implementor can maintain a mathematical property
    // about the object that provides the elim function.
    spec fn inv(&self) -> bool;
    spec fn post(&self) -> spec_fn(out:⟦P⟧) -> bool;

    proof fn elim(tracked &'static self) -> (tracked out:⟦P⟧)
        requires self.inv()
        ensures self.post()(out);
}

/// model for dyn □_tr
#[verifier(external_body)]
#[verifier::reject_recursive_types(⟦P⟧)]
struct dyn_□_tr<⟦P⟧> {
    _phantom : std::marker::PhantomData<(⟦P⟧)>,
}
impl<⟦P⟧> □_tr<⟦P⟧> for dyn_□_tr<⟦P⟧> {
    spec fn inv(&self) -> bool;
    spec fn post(&self) -> spec_fn(out:⟦P⟧) -> bool;

    #[verifier(external_body)]
    proof fn elim(tracked &'static self) -> (tracked out:⟦P⟧)
    {
        unimplemented!()
    }
}
impl<⟦P⟧> dyn_□_tr<⟦P⟧> {
    #[verifier(external_body)]
    proof fn from<T:□_tr<⟦P⟧>>(tracked x:T) -> (tracked r:Self)
        requires x.inv()
        ensures  r.post() == x.post(),
        r.inv(),
    {
        unimplemented!()
    }
}
#[verifier::reject_recursive_types(⟦P⟧)]
struct ⟦□⟧<⟦P⟧: 'static> {
    x:&'static dyn_□_tr<⟦P⟧>
}
impl<⟦P⟧> Duplicable for ⟦□⟧<⟦P⟧> {
    proof fn dup(tracked &self) -> (tracked r:Self) {
        return ⟦□⟧{
            x: self.x
        }
    }
}
impl<⟦P⟧> □_tr<⟦P⟧> for ⟦□⟧<⟦P⟧> {
    spec fn inv(&self) -> bool {
        self.x.inv()
    }

    spec fn post(&self) -> spec_fn(out:⟦P⟧) -> bool {
        self.x.post()
    }

    proof fn elim(tracked &self) -> (tracked out:⟦P⟧)
    {
        self.x.elim()
    }
}
impl<⟦P⟧> ⟦□⟧<⟦P⟧> {
    // FIXME: want to leak something to &'static in proof code
    #[verifier(external_body)]
    proof fn from<T:□_tr<⟦P⟧>>(tracked x:T) -> (tracked r:Self)
        requires x.inv()
        ensures r.post() == x.post(),
        r.inv(),
    {
        let tracked y = dyn_□_tr::from(x);
        let tracked z: &'static _ = Box::leak(Box::new(y));
        return ⟦□⟧{
            x: z
        };
    }
}
// XXX:
// Q: Should we take the ⟨P⟩ as input in the dup lemma, or should the lemma
// extract it from the ⟦□⟧ object?
// A: Can do best of both. Use the ⟨□⟩ style for stating, but the "extracting
// via spec fn" style for lemma. So, having ⟦□⟧ impl the trait.
spec fn ⟨□⟩<⟦P⟧>(⟨P⟩:spec_fn(⟦P⟧) -> bool) -> spec_fn(⟦□⟧<⟦P⟧>) -> bool {
    |res:⟦□⟧<⟦P⟧>| {
        res.post() == ⟨P⟩ &&
        res.inv()
    }
}


type Name = nat;
type Namespace = Set<Name>;
#[verifier(external_body)]
struct inv_mask {}
impl View for inv_mask {
    type V = Namespace;
    spec fn view(&self) -> Namespace;
}

/// model for dyn fupd_tr; TODO: don't even have the fupd_tr right now, because
/// we might not need it.
#[verifier(external_body)]
#[verifier::reject_recursive_types(⟦P⟧)]
struct ⟦fupd⟧<⟦P⟧> {
    _phantom : std::marker::PhantomData<(⟦P⟧)>,
}
spec fn ⟨fupd⟩<⟦P⟧>(Eo:Namespace, Ei:Namespace, ⟨P⟩:spec_fn(⟦P⟧) -> bool)
    -> spec_fn(⟦fupd⟧<⟦P⟧>) -> bool {
    |res:⟦fupd⟧<⟦P⟧>| {
        res.post() == ⟨P⟩ &&
        res.get_Eo() =~= Eo &&
        res.get_Ei() =~= Ei
    }
}
impl<⟦P⟧> ⟦fupd⟧<⟦P⟧> {
    spec fn get_Eo(&self) -> Namespace;
    spec fn get_Ei(&self) -> Namespace;
    spec fn post(&self) -> spec_fn(inner:⟦P⟧) -> bool;

    #[verifier(external_body)]
    proof fn elim(tracked self, tracked E:&mut inv_mask)
        -> (tracked ret:⟦P⟧)
      requires old(E)@ == self.get_Eo()
      ensures E@ == self.get_Ei(),
        self.post()(ret)
    {
        unimplemented!()
    }
}

/// Later credit
#[verifier(external_body)]
struct ⟦£⟧ {}

spec fn ⟨£⟩(n:nat) ->
    spec_fn(⟦£⟧) -> bool;

/// inv N P
#[verifier::reject_recursive_types(⟦P⟧)]
type ⟦inv⟧<⟦P⟧> =
    ⟦□⟧<⟦∀⟧<Namespace, ⟦-∗⟧<Pure, ⟦-∗⟧<⟦£⟧, ⟦fupd⟧<⟦∗⟧<⟦P⟧, ⟦-∗⟧<⟦P⟧, ⟦fupd⟧<True>>>>>>>>;

spec fn ⟨inv⟩<⟦P⟧>(N:Name, ⟨P⟩:spec_fn(⟦P⟧) -> bool)
    -> spec_fn(⟦inv⟧<⟦P⟧>) -> bool {
    ⟨□⟩(⟨∀⟩(|E:Namespace|
        ⟨-∗⟩(
        ⌜ E.contains(N) ⌝,
        ⟨-∗⟩(⟨£⟩(1), ⟨fupd⟩(E, E.remove(N), ⟨∗⟩(⟨P⟩,
                                ⟨-∗⟩(⟨P⟩, ⟨fupd⟩(E.remove(N), E, ⌜ true ⌝))
        )
    )))))
}

#[verifier(external_body)]
proof fn alloc_inv<⟦P⟧>(tracked E:&inv_mask, N:Name, ⟨P⟩:spec_fn(⟦P⟧) -> bool)
    -> (r:⟦inv⟧<⟦P⟧>)
    ensures ⟨inv⟩(N, ⟨P⟩)(r)
{
    unimplemented!()
}


type ⟦inv_closer⟧<⟦P⟧> = ⟦-∗⟧<⟦P⟧, ⟦fupd⟧<True>>;
spec fn ⟨inv_closer⟩<⟦P⟧>(E:Namespace, N:Name, ⟨P⟩:spec_fn(⟦P⟧) -> bool)
    -> spec_fn(⟦inv_closer⟧<⟦P⟧>) -> bool
{
    ⟨-∗⟩(⟨P⟩, ⟨fupd⟩(E, E.insert(N), ⌜ true ⌝))
}

proof fn inv_open<⟦P⟧>(N:Name, ⟨P⟩:spec_fn(⟦P⟧) -> bool,
                       tracked E:&mut inv_mask,
                       tracked Hi:⟦inv⟧<⟦P⟧>, tracked Hlc:⟦£⟧)
    -> (tracked r:(⟦P⟧, ⟦inv_closer⟧<⟦P⟧>))
    requires old(E)@.contains(N),
            holds(Hlc, ⟨£⟩(1)),
            holds(Hi, ⟨inv⟩(N, ⟨P⟩))
    ensures
      E@ == old(E)@.remove(N),
      ⟨P⟩(r.0),
      ⟨inv_closer⟩(E@, N, ⟨P⟩)(r.1)
{
    let tracked (P, Hclose) = Hi.dup().elim().instantiate(E@).instantiate(()).
        instantiate(Hlc).elim(E);
    return (P, Hclose);
}

proof fn inv_close<⟦P⟧>(N:Name, ⟨P⟩:spec_fn(⟦P⟧) -> bool,
                        tracked E:&mut inv_mask,
                        tracked HP:⟦P⟧,
                        tracked Hclose:⟦inv_closer⟧<⟦P⟧>)
    requires
      holds(HP, ⟨P⟩),
      holds(Hclose, ⟨inv_closer⟩(old(E)@, N, ⟨P⟩))
    ensures
      E@ == old(E)@.insert(N)
{
    Hclose.instantiate(HP).elim(E);
}

spec fn holds<X>(x:X, f:spec_fn(X) -> bool) -> bool {
    f(x)
}

////////////////////////////////////////////////////////////////////////////////
// General resources

type gname = nat;

#[verifier(external_body)]
struct ⟦tok_points_to⟧ {
}
spec fn ⟨tok_points_to⟩(γ:gname, k:u64) -> spec_fn(⟦tok_points_to⟧) -> bool;


#[verifier(external_body)]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(T)]
struct ⟦mlist_ptsto⟧<K,T> {
    _phantom1 : std::marker::PhantomData<K>,
    _phantom2 : std::marker::PhantomData<T>,
}
impl<K,T> ⟦mlist_ptsto⟧<K,T> {
    spec fn γ(&self) -> gname;
    spec fn key(&self) -> K;
    spec fn l(&self) -> Seq<T>;
}
spec fn ⟨mlist_ptsto⟩<K,T>(γ:gname, key:K, l:Seq<T>) -> spec_fn(⟦mlist_ptsto⟧<K,T>) -> bool {
    |res:⟦mlist_ptsto⟧<_,_>| {
        &&& res.γ() == γ
        &&& res.key() == key
        &&& res.l() == l
    }
}


#[verifier(external_body)]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(T)]
struct ⟦mlist_ptsto_lb⟧<K,T> {
    _phantom1 : std::marker::PhantomData<K>,
    _phantom2 : std::marker::PhantomData<T>,
}
impl<K,T> ⟦mlist_ptsto_lb⟧<K,T> {
    spec fn γ(&self) -> gname;
    spec fn key(&self) -> K;
    spec fn l(&self) -> Seq<T>;
}
spec fn ⟨mlist_ptsto_lb⟩<K,T>(γ:gname, key:K, l:Seq<T>) -> spec_fn(⟦mlist_ptsto_lb⟧<K,T>) -> bool {
    |res:⟦mlist_ptsto_lb⟧<_,_>| {
        &&& res.γ() == γ
        &&& res.key() == key
        &&& res.l() == l
    }
}

impl<K,T> Duplicable for ⟦mlist_ptsto_lb⟧<K,T> {
    #[verifier(external_body)]
    proof fn dup(tracked &self) -> (tracked r:Self) { unimplemented!() }
}

                 
#[verifier(external_body)]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(T)]
struct ⟦mlist_ptsto_ro⟧<K,T> {
    _phantom1 : std::marker::PhantomData<K>,
    _phantom2 : std::marker::PhantomData<T>,
}
impl<K,T> Duplicable for ⟦mlist_ptsto_ro⟧<K,T> {
    #[verifier(external_body)]
    proof fn dup(tracked &self) -> (tracked r:Self) { unimplemented!() }
}
impl<K,T> ⟦mlist_ptsto_ro⟧<K,T> {
    spec fn γ(&self) -> gname;
    spec fn key(&self) -> K;
    spec fn l(&self) -> Seq<T>;
}
spec fn ⟨mlist_ptsto_ro⟩<K,T>(γ:gname, key:K, l:Seq<T>) -> spec_fn(⟦mlist_ptsto_ro⟧<K,T>) -> bool {
    |res:⟦mlist_ptsto_ro⟧<_,_>| {
        &&& res.γ() == γ
        &&& res.key() == key
        &&& res.l() == l
    }
}


#[verifier(external_body)]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(T)]
struct ⟦mlist_ptsto_half⟧<K,T> {
    _phantom1 : std::marker::PhantomData<K>,
    _phantom2 : std::marker::PhantomData<T>,
}
impl<K,T> ⟦mlist_ptsto_half⟧<K,T> {
    spec fn γ(&self) -> gname;
    spec fn key(&self) -> K;
    spec fn l(&self) -> Seq<T>;
}
spec fn ⟨mlist_ptsto_half⟩<K,T>(γ:gname, key:K, l:Seq<T>) -> spec_fn(⟦mlist_ptsto_half⟧<K,T>) -> bool {
    |res:⟦mlist_ptsto_half⟧<_,_>| {
        &&& res.γ() == γ
        &&& res.key() == key
        &&& res.l() == l
    }
}

#[verifier(external_body)]
proof fn mlist_ptsto_lb_comparable<K,T>(
    tracked Hlb1: &⟦mlist_ptsto_lb⟧<K,T>,
    tracked Hlb2: &⟦mlist_ptsto_lb⟧<K,T>,
)
requires
  Hlb1.γ() == Hlb2.γ(),
  Hlb1.key() == Hlb2.key(),
ensures
  Hlb1.l().is_prefix_of(Hlb2.l()) || Hlb2.l().is_prefix_of(Hlb1.l())
{
    unimplemented!()
}


#[verifier(external_body)]
proof fn mlist_ptsto_update<K,T>(
    l_p:Seq<T>,
    tracked Hptsto: ⟦mlist_ptsto⟧<K,T>,
) -> (tracked Hout:⟦mlist_ptsto⟧<K,T>)
requires
  Hptsto.l().is_prefix_of(l_p),
ensures
  holds(Hout, ⟨mlist_ptsto⟩(Hptsto.γ(), Hptsto.key(), l_p)),
{
    unimplemented!()
}

// XXX: a bit of cleverness here using the "&" to make it so the old resource
// doesn't go away.
#[verifier(external_body)]
proof fn mlist_ptsto_get_lb<K,T>(
    γ:gname, k:K, l:Seq<T>,
    tracked Hptsto: &⟦mlist_ptsto⟧<K,T>,
) -> (tracked Hout:⟦mlist_ptsto_lb⟧<K,T>)
requires
  holds(*Hptsto, ⟨mlist_ptsto⟩(γ, k, l)),
ensures
  holds(Hout, ⟨mlist_ptsto_lb⟩(γ, k, l)),
{
    unimplemented!()
}

#[verifier(external_body)]
proof fn mlist_ptsto_lb_mono<K,T>(
    l_p:Seq<T>,
    tracked Hptsto: &⟦mlist_ptsto_lb⟧<K,T>,
) -> (tracked Hout:⟦mlist_ptsto_lb⟧<K,T>)
requires
  l_p.is_prefix_of(Hptsto.l()),
ensures
  holds(Hout, ⟨mlist_ptsto_lb⟩(Hptsto.γ(), Hptsto.key(), l_p)),
{
    unimplemented!()
}

#[verifier(external_body)]
proof fn mlist_ptsto_half_combine<K,T>(
    tracked Hptsto1: ⟦mlist_ptsto_half⟧<K,T>,
    tracked Hptsto2: ⟦mlist_ptsto_half⟧<K,T>,
) -> (tracked Hptsto:⟦mlist_ptsto⟧<K,T>)
requires
  Hptsto1.γ() == Hptsto2.γ(),
  Hptsto1.key() == Hptsto2.key(),
ensures
  Hptsto1.l() == Hptsto2.l(),
  holds(Hptsto, ⟨mlist_ptsto⟩(Hptsto1.γ(), Hptsto.key(), Hptsto.l())),
{
    unimplemented!()
}

#[verifier(external_body)]
proof fn mlist_ptsto_half_split<K,T>(
    γ:gname, k:K, l:Seq<T>,
    tracked Hptsto: ⟦mlist_ptsto⟧<K,T>,
) -> (tracked Hptstos:(⟦mlist_ptsto_half⟧<K,T>, ⟦mlist_ptsto_half⟧<K,T>))
requires
  holds(Hptsto, ⟨mlist_ptsto⟩(γ, k, l)),
ensures
  holds(Hptstos.0, ⟨mlist_ptsto_half⟩(γ, k, l)),
  holds(Hptstos.1, ⟨mlist_ptsto_half⟩(γ, k, l)),
{
    unimplemented!()
}

#[verifier(external_body)]
proof fn mlist_ptsto_half_get_lb<K,T>(
    tracked Hptsto: &⟦mlist_ptsto_half⟧<K,T>,
) -> (tracked Hout:⟦mlist_ptsto_lb⟧<K,T>)
ensures
  holds(Hout, ⟨mlist_ptsto_lb⟩(Hptsto.γ(), Hptsto.key(), Hptsto.l())),
{
    unimplemented!()
}

////////////////////////////////////////////////////////////////////////////////
// Paxos separation logic theory

struct mp_system_names {
    proposal_gn : gname,
    state_gn : gname,
}

struct mp_server_names {
    accepted_gn : gname,
    vote_gn : gname,
}

trait Finite {
    broadcast proof fn set_is_finite(s:Set<Self>) where Self: std::marker::Sized
        ensures s.finite();
}

impl Finite for u64 {
    #[verifier(external_body)]
    proof fn set_is_finite(s:Set<Self>) {
    }
}

// FIXME(verus): Causes cyclic self-refernce in definition
// broadcast use Finite::set_is_finite;
// broadcast use u64::set_is_finite;

/// A big_sepS requires that the set passed in be finite. When the type K is
/// itself a finite type, can use Finite::set_is_finite to conclude this. In many
/// proofs that modify the domain of a big_sepS, it is currently necessary to
/// prove this because `restrict` and `remove_keys` do not obviously result in a
/// finite domain.
#[verifier::reject_recursive_types(K)]
struct ⟦[∗ set]⟧<K, ⟦R⟧> {
    contents: Map<K, ⟦R⟧>
}
spec fn ⟨[∗ set]⟩<K, ⟦R⟧>(s:Set<K>, ⟨R⟩:spec_fn(K) -> spec_fn(⟦R⟧) -> bool)
                           -> spec_fn(⟦[∗ set]⟧<K, ⟦R⟧>) -> bool {
    |res:⟦[∗ set]⟧<K, ⟦R⟧>| {
        &&& res.contents.dom().finite()
        &&& res.contents.dom() =~= s
        &&& forall |k| s.contains(k) ==> ⟨R⟩(k)(#[trigger] res.contents[k])
    }
}
impl<K, ⟦R⟧:Duplicable> Duplicable for ⟦[∗ set]⟧<K,⟦R⟧> {
    #[verifier(external_body)]
    proof fn dup(tracked &self) -> (tracked r:Self) {
        unimplemented!()
    }
}

type EntryType = StateType;

type ⟦own_proposal⟧ = ⟦mlist_ptsto⟧<u64, EntryType>;
spec fn ⟨own_proposal⟩(γsys:mp_system_names, epoch:u64, σ:Seq<EntryType>) ->
    spec_fn(⟦own_proposal⟧) -> bool
{
    ⟨mlist_ptsto⟩(γsys.proposal_gn, epoch, σ)
}

type ⟦is_proposal_lb⟧ = ⟦mlist_ptsto_lb⟧<u64, EntryType>;
spec fn ⟨is_proposal_lb⟩(γsys:mp_system_names, epoch:u64, σ:Seq<EntryType>) ->
    spec_fn(⟦is_proposal_lb⟧) -> bool
{
    ⟨mlist_ptsto_lb⟩(γsys.proposal_gn, epoch, σ)
}


type ⟦own_vote_tok⟧ = ⟦tok_points_to⟧;
spec fn ⟨own_vote_tok⟩(γsrv:mp_server_names, epoch:u64) -> spec_fn(⟦own_vote_tok⟧) -> bool {
    |res| {
        ⟨tok_points_to⟩(γsrv.vote_gn, epoch)(res)
    }
}


type ⟦is_accepted_lb⟧ = ⟦mlist_ptsto_lb⟧<u64, EntryType>;
spec fn ⟨is_accepted_lb⟩(γsrv:mp_server_names, epoch:u64, σ:Seq<EntryType>) ->
    spec_fn(⟦is_proposal_lb⟧) -> bool
{
    ⟨mlist_ptsto_lb⟩(γsrv.accepted_gn, epoch, σ)
}

type ⟦own_accepted⟧ = ⟦mlist_ptsto⟧<u64, EntryType>;
spec fn ⟨own_accepted⟩(γsrv:mp_server_names, epoch:u64, σ:Seq<EntryType>) ->
    spec_fn(⟦own_accepted⟧) -> bool
{
    ⟨mlist_ptsto⟩(γsrv.accepted_gn, epoch, σ)
}

type ⟦is_accepted_ro⟧ = ⟦mlist_ptsto_ro⟧<u64, EntryType>;
spec fn ⟨is_accepted_ro⟩(γsrv:mp_server_names, epoch:u64, l:Seq<EntryType>) ->
    spec_fn(⟦is_accepted_ro⟧) -> bool
{
    ⟨mlist_ptsto_ro⟩(γsrv.accepted_gn, epoch, l)
}


// own_commit is half ownership of a mlist_ptsto with key 0
type ⟦own_commit⟧ = ⟦mlist_ptsto_half⟧<u64, EntryType>;
spec fn ⟨own_commit⟩(γsys:mp_system_names, σ:Seq<EntryType>) ->
    spec_fn(⟦own_commit⟧) -> bool
{
    ⟨mlist_ptsto_half⟩(γsys.state_gn, 0, σ)
}

type ⟦is_commit_lb⟧ = ⟦mlist_ptsto_lb⟧<u64, EntryType>;
spec fn ⟨is_commit_lb⟩(γsys:mp_system_names, σ:Seq<EntryType>) ->
    spec_fn(⟦is_commit_lb⟧) -> bool
{
    ⟨mlist_ptsto_lb⟩(γsys.state_gn, 0, σ)
}


type Config = Set<mp_server_names>;

struct ⟦is_committed_by⟧ {
    Hacc_lbs : ⟦[∗ set]⟧<mp_server_names, ⟦is_accepted_lb⟧>
}
#[verifier::opaque]
spec fn W_trigger(W:Set<mp_server_names>) -> bool { true }
spec fn ⟨is_committed_by⟩(config:Config, epoch:u64, σ:Seq<EntryType>)
    -> spec_fn(⟦is_committed_by⟧) -> bool
{
    |res:⟦is_committed_by⟧| {
    exists |W:Set<mp_server_names>| {
        #[trigger] W_trigger(W) &&
        W.subset_of(config) &&
        2 * W.len() > config.len() &&
        holds(
            res.Hacc_lbs,
            ⟨[∗ set]⟩(W, |γsrv| ⟨is_accepted_lb⟩(γsrv, epoch, σ))
        )
    }}
}
impl Duplicable for ⟦is_committed_by⟧ {
    proof fn dup(tracked &self) -> (tracked r:Self) {
        return ⟦is_committed_by⟧ {
            Hacc_lbs: self.Hacc_lbs.dup()
        };
    }
}


type ⟦old_proposal_max⟧ =
    ⟦□⟧<⟦∀⟧<(u64, Seq<EntryType>),
        ⟦-∗⟧<Pure, 
            ⟦-∗⟧<⟦is_committed_by⟧, Pure>>>>;
spec fn ⟨old_proposal_max⟩(config:Set<mp_server_names>, γsys:mp_system_names, epoch:u64, σ:Seq<EntryType>)
    -> spec_fn(⟦old_proposal_max⟧) -> bool {
    ⟨□⟩(
    ⟨∀⟩(|f:(u64,Seq<EntryType>)| {
            let epoch_old = f.0;
            let σ_old = f.1;
            ⟨-∗⟩(
              ⌜ epoch_old < epoch ⌝,
              ⟨-∗⟩(
                ⟨is_committed_by⟩(config, epoch_old, σ_old),
                ⌜ σ_old.is_prefix_of(σ) ⌝))
        }
    )
    )
}

spec const ⊤ : Namespace = Set::new(|_p| true);
spec const replN : Name = 1;
type ⟦is_proposal_valid⟧ =
⟦□⟧<⟦∀⟧<Seq<EntryType>,
        ⟦-∗⟧<Pure, ⟦-∗⟧<⟦own_commit⟧, ⟦fupd⟧<⟦own_commit⟧>>>
>>;
spec fn ⟨is_proposal_valid⟩(γsys:mp_system_names, σ:Seq<EntryType>)
    -> spec_fn(⟦is_proposal_valid⟧) -> bool {
    ⟨□⟩(
    ⟨∀⟩(|σ_p:Seq<EntryType>| {
      ⟨-∗⟩(⌜ σ_p.is_prefix_of(σ) ⌝,
             ⟨-∗⟩(⟨own_commit⟩(γsys, σ_p),
                    ⟨fupd⟩(⊤.remove(replN), ⊤.remove(replN), ⟨own_commit⟩(γsys, σ))))
    })
    )
}

type ⟦is_proposal_facts⟧ = ⟦∗⟧<⟦old_proposal_max⟧, ⟦is_proposal_valid⟧>;
spec fn ⟨is_proposal_facts⟩(config:Set<mp_server_names>, γsys:mp_system_names, epoch:u64, σ:Seq<EntryType>) ->
    spec_fn(⟦is_proposal_facts⟧) -> bool
{
    ⟨∗⟩(
        ⟨old_proposal_max⟩(config, γsys, epoch, σ),
        ⟨is_proposal_valid⟩(γsys, σ),
    )
}


type ⟦is_accepted_upper_bound⟧ =
⟦∗⟧<⟦∃⟧<Seq<EntryType>, ⟦∗⟧<Pure, ⟦is_accepted_ro⟧,>>,
    ⟦□⟧<⟦∀⟧<u64, ⟦-∗⟧<Pure, ⟦is_accepted_ro⟧>>>>;
spec fn lt(a:u64, b:u64) -> bool {
    a < b
}
spec fn ⟨is_accepted_upper_bound⟩(γsrv:mp_server_names, log:Seq<EntryType>, acceptedEpoch:u64, newEpoch:u64)
                                  -> spec_fn(⟦is_accepted_upper_bound⟧) -> bool
{
    ⟨∗⟩(⟨∃⟩(|logPrefix:Seq<EntryType>| {
        ⟨∗⟩(⌜ logPrefix.is_prefix_of(log) ⌝,
            ⟨is_accepted_ro⟩(γsrv, acceptedEpoch, logPrefix))
    }),
    ⟨□⟩(⟨∀⟩(|epoch_p:u64| {
        ⟨-∗⟩(
            ⌜ lt(acceptedEpoch, epoch_p) && lt(epoch_p, newEpoch) ⌝,
            ⟨is_accepted_ro⟩(γsrv, epoch_p, Seq::empty())
            )
    })))
}


struct ⟦own_replica_ghost⟧ {
    Hprop_lb : ⟦is_proposal_lb⟧,
    Hprop_facts : ⟦is_proposal_facts⟧,
    Hacc_lb : ⟦is_accepted_lb⟧,
    HepochIneq : Pure,
    Hacc : ⟦own_accepted⟧,
    Hacc_ub : ⟦or⟧<Pure, ⟦is_accepted_upper_bound⟧>,
    Hunused : ⟦[∗ set]⟧<u64, ⟦own_accepted⟧>,
    Hvotes : ⟦[∗ set]⟧<u64, ⟦own_vote_tok⟧>,
}

ghost struct MPaxosState {
    epoch : u64,
    accepted_epoch : u64,
    log : Seq<EntryType>,
}
spec fn ⟨own_replica_ghost⟩(config:Config, γsys:mp_system_names, γsrv:mp_server_names, st:MPaxosState) 
    -> spec_fn(⟦own_replica_ghost⟧) -> bool {
    |res:⟦own_replica_ghost⟧| {
        holds(res.Hprop_lb, ⟨is_proposal_lb⟩(γsys, st.accepted_epoch, st.log)) &&
        holds(res.Hprop_facts, ⟨is_proposal_facts⟩(config, γsys, st.accepted_epoch, st.log)) &&
        holds(res.Hacc_lb, ⟨is_accepted_lb⟩(γsrv, st.accepted_epoch, st.log)) &&
        holds(res.HepochIneq, ⌜ st.accepted_epoch <= st.epoch ⌝) &&
        holds(res.Hacc, ⟨own_accepted⟩(γsrv, st.epoch, if (st.accepted_epoch == st.epoch) {
                    st.log
                } else {
                    Seq::empty()
                })) &&
        holds(res.Hacc_ub, ⟨or⟩(
            ⌜ !(st.accepted_epoch < st.epoch) ⌝,
            ⟨is_accepted_upper_bound⟩(γsrv, st.log, st.accepted_epoch, st.epoch)
        )) &&
        holds(res.Hunused, ⟨[∗ set]⟩(
            Set::new(|e:u64| e > st.epoch),
            |e| ⟨own_accepted⟩(γsrv, e, Seq::empty())
        )) &&
        holds(res.Hvotes, ⟨[∗ set]⟩(
            Set::new(|e:u64| e > st.epoch),
            |e| ⟨own_vote_tok⟩(γsrv, e)
        ))
    }
}

proof fn ghost_replica_get_lb(
    config:Config,
    γsys:mp_system_names,
    γsrv:mp_server_names,
    st:MPaxosState,
    tracked Hown: &⟦own_replica_ghost⟧,
) ->
(tracked ret: ⟦is_accepted_lb⟧)
  requires holds(*Hown, ⟨own_replica_ghost⟩(config, γsys, γsrv, st)),
  ensures
    ⟨is_accepted_lb⟩(γsrv, st.accepted_epoch, st.log)(ret)
{
    mlist_ptsto_lb_mono(st.log, &Hown.Hacc_lb)
}

proof fn ghost_replica_accept_same_epoch(
    config:Config,
    γsys:mp_system_names,
    γsrv:mp_server_names,
    st:MPaxosState,
    epoch_p:u64,
    log_p: Seq<EntryType>,
    tracked Hown: ⟦own_replica_ghost⟧,
    tracked Hprop_lb: ⟦is_proposal_lb⟧,
    tracked Hprop_facts: ⟦is_proposal_facts⟧,
) ->
(tracked ret: ⟦own_replica_ghost⟧)
  requires
    st.epoch <= epoch_p,
    st.accepted_epoch == epoch_p,
    st.log.len() <= log_p.len(),
    holds(Hown, ⟨own_replica_ghost⟩(config, γsys, γsrv, st)),
    holds(Hprop_lb, ⟨is_proposal_lb⟩(γsys, epoch_p, log_p)),
    holds(Hprop_facts, ⟨is_proposal_facts⟩(config, γsys, epoch_p, log_p)),
  ensures
    st.epoch == epoch_p,
    ⟨own_replica_ghost⟩(config, γsys, γsrv, MPaxosState{epoch:epoch_p, accepted_epoch:epoch_p, log:log_p})(ret)
{
    let tracked mut Hown = Hown;
    // assert (st.epoch == epoch_p);
    // assert (st.accepted_epoch == st.epoch);
    mlist_ptsto_lb_comparable(&Hown.Hprop_lb, &Hprop_lb);
    // assert(st.log.is_prefix_of(log_p));
    Hown.Hacc = mlist_ptsto_update(log_p, Hown.Hacc);
    Hown.Hacc_lb = mlist_ptsto_get_lb(γsrv.accepted_gn, epoch_p, log_p, &Hown.Hacc);
    Hown.Hprop_lb = Hprop_lb;
    Hown.Hprop_facts = Hprop_facts;
    Hown.Hacc_ub = ⟦or⟧::Left(());
    return Hown;
}

proof fn ghost_replica_accept_same_epoch_old(
    config:Config,
    γsys:mp_system_names,
    γsrv:mp_server_names,
    st:MPaxosState,
    epoch_p:u64,
    log_p: Seq<EntryType>,
    tracked Hown: &⟦own_replica_ghost⟧,
    tracked Hprop_lb: &⟦is_proposal_lb⟧,
    tracked Hprop_facts: &⟦is_proposal_facts⟧,
) ->
(tracked ret: ⟦is_accepted_lb⟧)
  requires
    st.epoch <= epoch_p,
    st.accepted_epoch == epoch_p,
    log_p.len() <= st.log.len(),
    holds(*Hown, ⟨own_replica_ghost⟩(config, γsys, γsrv, st)),
    holds(*Hprop_lb, ⟨is_proposal_lb⟩(γsys, epoch_p, log_p)),
    holds(*Hprop_facts, ⟨is_proposal_facts⟩(config, γsys, epoch_p, log_p)),
  ensures
    ⟨is_accepted_lb⟩(γsrv, epoch_p, log_p)(ret)
{
    mlist_ptsto_lb_comparable(&Hown.Hprop_lb, &Hprop_lb);
    mlist_ptsto_lb_mono(log_p, &Hown.Hacc_lb)
}

// This is the first complicated lemma. The other ones are not that bad.
proof fn ghost_replica_accept_new_epoch(
    config:Config,
    γsys:mp_system_names,
    γsrv:mp_server_names,
    st:MPaxosState,
    epoch_p:u64,
    log_p: Seq<EntryType>,
    tracked Hown: ⟦own_replica_ghost⟧,
    tracked Hprop_lb: ⟦is_proposal_lb⟧,
    tracked Hprop_facts: ⟦is_proposal_facts⟧,
) ->
(tracked ret: ⟦own_replica_ghost⟧)
  requires
    st.epoch <= epoch_p,
    st.accepted_epoch != epoch_p,
    holds(Hown, ⟨own_replica_ghost⟩(config, γsys, γsrv, st)),
    holds(Hprop_lb, ⟨is_proposal_lb⟩(γsys, epoch_p, log_p)),
    holds(Hprop_facts, ⟨is_proposal_facts⟩(config, γsys, epoch_p, log_p)),
  ensures
    ⟨own_replica_ghost⟩(config, γsys, γsrv, MPaxosState{epoch:epoch_p, accepted_epoch:epoch_p, log:log_p})(ret)
{
    broadcast use Finite::set_is_finite; // XXX: needed for big_sepS
    let tracked mut Hown = Hown;
    let st_p = MPaxosState{epoch:epoch_p, accepted_epoch:epoch_p, log:log_p};
    Hown.Hprop_lb = Hprop_lb;
    Hown.Hprop_facts = Hprop_facts;
    Hown.Hacc_ub = ⟦or⟧::Left(());
    if st.epoch < epoch_p {
        Hown.Hunused.contents.tracked_remove_keys(Set::new(|e:u64| st.epoch < e < st_p.epoch));
        let tracked mut Hacc = Hown.Hunused.contents.tracked_remove(epoch_p);
        Hacc = mlist_ptsto_update(log_p, Hacc);
        let tracked Hacc_lb = mlist_ptsto_get_lb(γsrv.accepted_gn, epoch_p, log_p, &Hacc);
        Hown.Hvotes.contents.tracked_remove_keys(Set::new(|e:u64| st.epoch < e < st_p.epoch));
        Hown.Hvotes.contents.tracked_remove(st_p.epoch);
        Hown.Hacc = Hacc;
        Hown.Hacc_lb = Hacc_lb;
        assert(Hown.Hvotes.contents.dom().finite());
        return Hown;
    } else if st.epoch == epoch_p {
        let tracked mut Hacc = mlist_ptsto_update(log_p, Hown.Hacc);
        let tracked Hacc_lb = mlist_ptsto_get_lb(γsrv.accepted_gn, epoch_p, log_p, &Hacc);
        Hown.Hacc = Hacc;
        Hown.Hacc_lb = Hacc_lb;
        return Hown;
    } else {
        assert(false);
        return Hown;
    }
}

/// Replication invariant.
tracked struct ⟦is_repl_inv_inner_ex⟧ {
    Hcommit : ⟦own_commit⟧,
    Hcommit_by: ⟦is_committed_by⟧,
    Hprop_lb: ⟦is_proposal_lb⟧,
    Hprop_facts: ⟦is_proposal_facts⟧,
}
type ⟦is_repl_inv_inner⟧ = ⟦∃⟧<(Seq<EntryType>, u64), ⟦is_repl_inv_inner_ex⟧>;
spec fn ⟨is_repl_inv_inner⟩(config:Set<mp_server_names>, γsys:mp_system_names)
    -> spec_fn(⟦is_repl_inv_inner⟧) -> bool
{
    ⟨∃⟩(
    |f:(Seq<_>, u64)| {
    let σ = f.0;
    let epoch = f.1;
    |res:⟦is_repl_inv_inner_ex⟧| {
        holds(res.Hcommit, ⟨own_commit⟩(γsys, σ)) &&
        holds(res.Hcommit_by, ⟨is_committed_by⟩(config, epoch, σ)) &&
        holds(res.Hprop_lb, ⟨is_proposal_lb⟩(γsys, epoch, σ)) &&
        holds(res.Hprop_facts, ⟨is_proposal_facts⟩(config, γsys, epoch, σ))
    }
    }
    )
}

type ⟦is_repl_inv⟧ = ⟦inv⟧<⟦is_repl_inv_inner⟧>;
spec fn ⟨is_repl_inv⟩(config:Set<mp_server_names>, γsys:mp_system_names)
    -> spec_fn(⟦is_repl_inv⟧) -> bool
{
    ⟨inv⟩(replN, ⟨is_repl_inv_inner⟩(config, γsys))
}

#[verifier(external_body)]
proof fn false_to_anything<A>() -> (tracked r:A)
    requires false
{
    unimplemented!();
}

proof fn ghost_commit(
    tracked E:&mut inv_mask,
    config:Config,
    γsys:mp_system_names,
    epoch:u64,
    σ: Seq<EntryType>,
    tracked Hlc: ⟦£⟧,
    tracked Hinv: ⟦is_repl_inv⟧,
    tracked Hcom: ⟦is_committed_by⟧,
    tracked Hprop_lb: ⟦is_proposal_lb⟧,
    tracked Hprop_facts: ⟦is_proposal_facts⟧,
) ->
(tracked ret: ⟦is_commit_lb⟧)
  requires
    old(E)@ =~= ⊤,
    holds(Hlc, ⟨£⟩(1)),
    holds(Hinv, ⟨is_repl_inv⟩(config, γsys)),
    holds(Hcom, ⟨is_committed_by⟩(config, epoch, σ)),
    holds(Hprop_lb, ⟨is_proposal_lb⟩(γsys, epoch, σ)),
    holds(Hprop_facts, ⟨is_proposal_facts⟩(config, γsys, epoch, σ)),
  ensures
    ⟨is_commit_lb⟩(γsys, σ)(ret),
    E@ == old(E)@,
{
    // open invariant
    let tracked (mut Hown, Hclose) = inv_open(replN, ⟨is_repl_inv_inner⟩(config, γsys),
             E, Hinv, Hlc);
    let tracked (Ghost(f), Hown) = Hown.destruct();
    let (σcommit, epoch_commit) : (Seq<_>, u64) = f;

    {
        if epoch < epoch_commit {
            Hown.Hprop_facts.0.dup().elim().instantiate((epoch, σ))
            .instantiate(())
            .instantiate(Hcom.dup());
        } else if epoch == epoch_commit {
            mlist_ptsto_lb_comparable(&Hprop_lb, &Hown.Hprop_lb);
        } else {
            Hprop_facts.0.dup().elim().instantiate((epoch_commit, σcommit))
            .instantiate(())
            .instantiate(Hown.Hcommit_by.dup());
        }
        assert(σcommit.is_prefix_of(σ) || σ.is_prefix_of(σcommit));
    }

    /* BUG: Verus thinks y is spec mode
    assert(σcommit.is_prefix_of(σ) || σ.is_prefix_of(σcommit)) by {
        if epoch < epoch_commit {
            let tracked y = Hown.Hprop_facts.0.dup();
            let tracked x = y.instantiate((epoch, σ));
        }
    }*/

    if σcommit.is_prefix_of(σ) {
        // update commit using is_prop_valid
        let tracked mut Hown = Hown; // XXX: due to Verus unsupported 
        let tracked Hprop_valid = Hprop_facts.1.dup().elim();
        let tracked Hcommit = Hprop_valid.instantiate(σcommit).
            instantiate(()).
            instantiate(Hown.Hcommit).
            elim(E);
        let tracked Hlb = mlist_ptsto_half_get_lb(&Hcommit);

        // close invariant
        Hown.Hcommit = Hcommit;
        Hown.Hprop_lb = Hprop_lb;
        Hown.Hprop_facts = Hprop_facts;
        Hown.Hcommit_by = Hcom;
        let tracked Hown = ⟦∃⟧::exists((σ, epoch), Hown);
        inv_close(replN, ⟨is_repl_inv_inner⟩(config, γsys), E, Hown, Hclose);

        return Hlb;
    } else if σ.is_prefix_of(σcommit) {
        // get lb from σcommit
        let tracked Hlb = mlist_ptsto_half_get_lb(&Hown.Hcommit);
        let tracked Hlb = mlist_ptsto_lb_mono(σ, &Hlb);
        // close invariant
        let tracked Hown = ⟦∃⟧::exists((σcommit, epoch_commit), Hown);
        inv_close(replN, ⟨is_repl_inv_inner⟩(config, γsys), E, Hown, Hclose);
        return Hlb;
    } else {
        assert(false);
        return false_to_anything();
    }
}

// This has all the closure context for proving the right hand conjunct is
// is_accepted_upper_bound for going to a new epoch.
tracked struct NewUbBox {
    ghost γsrv: mp_server_names,
    ghost acceptedEpoch: u64,
    ghost acceptedEpoch_p: u64,
    ghost newEpoch: u64,
    ghost epoch_p: u64, // unused for most
    tracked HoldWand: ⟦□⟧<⟦∀⟧<u64, ⟦-∗⟧<Pure, ⟦is_accepted_ro⟧>>>
}
impl NewUbBox {
    spec fn concrete_inv(&self) -> bool {
        self.acceptedEpoch < self.acceptedEpoch_p &&
        self.acceptedEpoch_p < self.newEpoch &&
        holds(self.HoldWand, ⟨□⟩(⟨∀⟩(|epoch_p:u64|{
            ⟨-∗⟩(⌜ lt(self.acceptedEpoch, epoch_p) && lt(epoch_p, self.newEpoch) ⌝,
                 ⟨is_accepted_ro⟩(self.γsrv, epoch_p, Seq::empty())
            )
        })))
    }
}

impl wand_tr<Pure, ⟦is_accepted_ro⟧> for NewUbBox {
    spec fn inv(&self) -> bool {
        self.concrete_inv()
    }

    spec fn pre(&self) -> spec_fn(Pure) -> bool {
        ⌜ lt(self.acceptedEpoch_p, self.epoch_p) && lt(self.epoch_p, self.newEpoch) ⌝
    }

    spec fn post(&self) -> spec_fn(⟦is_accepted_ro⟧) -> bool {
        ⟨is_accepted_ro⟩(self.γsrv, self.epoch_p, Seq::empty())
    }

    proof fn instantiate(tracked self, tracked i:Pure) -> (tracked out:⟦is_accepted_ro⟧) {
        return self.HoldWand.elim().instantiate(self.epoch_p).instantiate(());
    }
}

impl ∀_tr<u64, ⟦-∗⟧<Pure, ⟦is_accepted_ro⟧>> for NewUbBox {
    spec fn inv(&self) -> bool {
        self.concrete_inv()
    }

    spec fn post(&self) -> spec_fn(u64) ->
        spec_fn(⟦-∗⟧<Pure, ⟦is_accepted_ro⟧>) -> bool
    {
        |epoch_p:u64| {
            ⟨-∗⟩(⌜ lt(self.acceptedEpoch_p, epoch_p) && lt(epoch_p, self.newEpoch) ⌝,
                 ⟨is_accepted_ro⟩(self.γsrv, epoch_p, Seq::empty()))
        }
    }

    proof fn instantiate(tracked self, epoch_p:u64) ->
        (tracked out: ⟦-∗⟧<Pure, ⟦is_accepted_ro⟧>)
    {
        let tracked mut s2 = self;
        s2.epoch_p = epoch_p;
        return ⟦-∗⟧::from(s2);
    }
}

impl □_tr<⟦∀⟧<u64, ⟦-∗⟧<Pure, ⟦is_accepted_ro⟧>>> for NewUbBox {
    spec fn inv(&self) -> bool {
        self.concrete_inv()
    }

    spec fn post(&self) ->
        spec_fn(⟦∀⟧<u64, ⟦-∗⟧<Pure, ⟦is_accepted_ro⟧>>) -> bool
    {
        (⟨∀⟩(|epoch_p:u64| {
            ⟨-∗⟩(⌜ lt(self.acceptedEpoch_p, epoch_p) && lt(epoch_p, self.newEpoch) ⌝,
                ⟨is_accepted_ro⟩(self.γsrv, epoch_p, Seq::empty()))
        }))
    }

    proof fn elim(tracked &'static self) -> (tracked out: ⟦∀⟧<u64, ⟦-∗⟧<Pure, ⟦is_accepted_ro⟧>>)
    {
        let tracked s2 = NewUbBox{
            γsrv: self.γsrv,
            acceptedEpoch: self.acceptedEpoch,
            acceptedEpoch_p: self.acceptedEpoch_p,
            newEpoch: self.newEpoch,
            epoch_p: self.epoch_p, // unused at this level
            HoldWand: self.HoldWand.dup()
        };
        return ⟦∀⟧::from(s2);
    }
}

proof fn accepted_upper_bound_mono_epoch(
    γsrv:mp_server_names,
    log: Seq<EntryType>,
    acceptedEpoch:u64,
    acceptedEpoch_p:u64,
    newEpoch:u64,
    tracked Hub: ⟦is_accepted_upper_bound⟧,
) ->
(tracked ret: ⟦is_accepted_upper_bound⟧)
  requires
    acceptedEpoch < acceptedEpoch_p,
    acceptedEpoch_p < newEpoch,
    holds(Hub, ⟨is_accepted_upper_bound⟩(γsrv, log, acceptedEpoch, newEpoch)),
  ensures
    holds(ret, ⟨is_accepted_upper_bound⟩(γsrv, Seq::empty(), acceptedEpoch_p, newEpoch)),
{
    let tracked Hwand = Hub.1.dup().elim();
    let tracked Hacc_ro = Hwand.instantiate(acceptedEpoch_p).instantiate(());
    let tracked Hleft = ⟦∃⟧::exists(Seq::empty(), ((), Hacc_ro));

    // produce the new □(∀ ...)
    let tracked w = NewUbBox{
        γsrv: γsrv,
        acceptedEpoch: acceptedEpoch,
        acceptedEpoch_p: acceptedEpoch_p,
        newEpoch: newEpoch,
        epoch_p: 0, // unused at this level
        HoldWand: Hub.1
    };
    let tracked Hright = ⟦□⟧::from(w);
    let tracked Hub2 = (Hleft, Hright);
    return Hub2;
}

fn main() {}
}
