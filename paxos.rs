#![allow(mixed_script_confusables)]
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
    spec fn pre(&self) -> spec_fn(x:P) -> bool;
    spec fn post(&self) -> spec_fn(x:Q) -> bool;

    proof fn instantiate(tracked self, tracked i:P) -> (tracked out:Q) where Self: std::marker::Sized
        requires self.pre()(i)
        ensures self.post()(out)
        opens_invariants none
        ;
}

/// model for dyn wand_tr
#[verifier(external_body)]
#[verifier::reject_recursive_types(⟦P⟧)]
#[verifier::reject_recursive_types(⟦Q⟧)]
struct ⟦wand⟧<⟦P⟧,⟦Q⟧> {
    _phantom : std::marker::PhantomData<(⟦P⟧,⟦Q⟧)>,
}
impl<⟦P⟧, ⟦Q⟧> wand_tr<⟦P⟧, ⟦Q⟧> for ⟦wand⟧<⟦P⟧, ⟦Q⟧> {
    spec fn pre(&self) -> spec_fn(x:⟦P⟧) -> bool;
    spec fn post(&self) -> spec_fn(x:⟦Q⟧) -> bool;

    #[verifier(external_body)]
    proof fn instantiate(tracked self, tracked i:⟦P⟧) -> (tracked out:⟦Q⟧) {
        unimplemented!();
    }
}
impl<⟦P⟧, ⟦Q⟧> ⟦wand⟧<⟦P⟧, ⟦Q⟧> {
    #[verifier(external_body)]
    proof fn from<T:wand_tr<⟦P⟧,⟦Q⟧>>(tracked x:T) -> (tracked r:Self)
        ensures r.pre() == x.pre(),
        r.post() == x.post(),
    {
        unimplemented!()
    }
}
spec fn ⟨wand⟩<⟦P⟧,⟦Q⟧>(⟨P⟩:spec_fn(⟦P⟧) -> bool, ⟨Q⟩:spec_fn(⟦Q⟧) -> bool)
    -> spec_fn(⟦wand⟧<⟦P⟧,⟦Q⟧>) -> bool {
    |res:⟦wand⟧<_,_>| {
        &&& res.pre() == ⟨P⟩
        &&& res.post() == ⟨Q⟩
    }
}



/// ∀ (x:X), A(x)   where A is a predicate.
trait forall_tr<X, ⟦A⟧> {
    spec fn post(&self) -> spec_fn(x:X) -> spec_fn(out:⟦A⟧) -> bool;

    proof fn instantiate(tracked self, x:X) -> (tracked out:⟦A⟧) where Self: std::marker::Sized
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
    spec fn post(&self) -> spec_fn(x:X) -> spec_fn(out:⟦A⟧) -> bool;

    #[verifier(external_body)]
    proof fn instantiate(tracked self, x:X) -> (tracked out:⟦A⟧) {
        unimplemented!();
    }
}
spec fn ⟨∀⟩<X,⟦A⟧>(⟨A⟩:spec_fn(x:X) -> spec_fn(out:⟦A⟧) -> bool)
    -> spec_fn(⟦∀⟧<X,⟦A⟧>) -> bool
{
    |res:⟦∀⟧<_,_>| {
        res.post() == ⟨A⟩
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


/// □ P
trait □_tr<⟦P⟧> {
    spec fn post(&self) -> spec_fn(out:⟦P⟧) -> bool;

    proof fn dup(&self) -> (tracked out:⟦P⟧)
        ensures self.post()(out)
        ;
}

/// model for dyn □_tr
#[verifier(external_body)]
#[verifier::reject_recursive_types(⟦P⟧)]
struct ⟦□⟧<⟦P⟧> {
    _phantom : std::marker::PhantomData<(⟦P⟧)>,
}
impl<⟦P⟧> □_tr<⟦P⟧> for ⟦□⟧<⟦P⟧> {
    spec fn post(&self) -> spec_fn(out:⟦P⟧) -> bool;

    #[verifier(external_body)]
    proof fn dup(&self) -> (tracked out:⟦P⟧) {
        unimplemented!();
    }
}
// XXX:
// Q: Should we take the ⟨P⟩ as input in the dup lemma, or should the lemma
// extract it from the ⟦□⟧ object?
// A: Can do best of both. Use the ⟨□⟩ style for stating, but the "extracting
// via spec fn" style for lemma. So, having ⟦□⟧ impl the trait.
spec fn ⟨□⟩<⟦P⟧>(⟨P⟩:spec_fn(⟦P⟧) -> bool) -> spec_fn(⟦□⟧<⟦P⟧>) -> bool {
    |res:⟦□⟧<⟦P⟧>| {
        res.post() == ⟨P⟩
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
    ⟦□⟧<⟦∀⟧<Namespace, ⟦wand⟧<Pure, ⟦wand⟧<⟦£⟧, ⟦fupd⟧<⟦sep⟧<⟦P⟧, ⟦wand⟧<⟦P⟧, ⟦fupd⟧<True>>>>>>>>;

spec fn ⟨inv⟩<⟦P⟧>(N:Name, ⟨P⟩:spec_fn(⟦P⟧) -> bool)
    -> spec_fn(⟦inv⟧<⟦P⟧>) -> bool {
    ⟨□⟩(⟨∀⟩(|E:Namespace|
        ⟨wand⟩(
        |_p| E.contains(N),
        ⟨wand⟩(⟨£⟩(1), ⟨fupd⟩(E, E.remove(N), ⟨sep⟩(⟨P⟩,
                                ⟨wand⟩(⟨P⟩, ⟨fupd⟩(E.remove(N), E, |_p| true))
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


type ⟦inv_closer⟧<⟦P⟧> = ⟦wand⟧<⟦P⟧, ⟦fupd⟧<True>>;
spec fn ⟨inv_closer⟩<⟦P⟧>(E:Namespace, N:Name, ⟨P⟩:spec_fn(⟦P⟧) -> bool)
    -> spec_fn(⟦inv_closer⟧<⟦P⟧>) -> bool
{
    ⟨wand⟩(⟨P⟩, ⟨fupd⟩(E, E.insert(N), |_p| true))
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
    // let tracked H = i.Hi.dup().instantiate(E@);
    let tracked (P, Hclose) = Hi.dup().instantiate(E@).instantiate(()).
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
spec fn ⟨mlist_ptsto⟩<K,T>(γ:gname, key:K, l:Seq<T>) -> spec_fn(⟦mlist_ptsto⟧<K,T>) -> bool;


#[verifier(external_body)]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(T)]
struct ⟦mlist_ptsto_lb⟧<K,T> {
    _phantom1 : std::marker::PhantomData<K>,
    _phantom2 : std::marker::PhantomData<T>,
}
spec fn ⟨mlist_ptsto_lb⟩<K,T>(γ:gname, key:K, l:Seq<T>) -> spec_fn(⟦mlist_ptsto_lb⟧<K,T>) -> bool;

                 
#[verifier(external_body)]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(T)]
struct ⟦mlist_ptsto_ro⟧<K,T> {
    _phantom1 : std::marker::PhantomData<K>,
    _phantom2 : std::marker::PhantomData<T>,
}
spec fn ⟨mlist_ptsto_ro⟩<K,T>(γ:gname, key:K, l:Seq<T>) -> spec_fn(⟦mlist_ptsto_ro⟧<K,T>) -> bool;


#[verifier(external_body)]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(T)]
struct ⟦mlist_ptsto_half⟧<K,T> {
    _phantom1 : std::marker::PhantomData<K>,
    _phantom2 : std::marker::PhantomData<T>,
}
spec fn ⟨mlist_ptsto_half⟩<K,T>(γ:gname, key:K, l:Seq<T>) -> spec_fn(⟦mlist_ptsto_half⟧<K,T>) -> bool;


#[verifier(external_body)]
proof fn mlist_ptsto_lb_comparable<K,T>(
    γ:gname, k:K, l:Seq<T>, l_p:Seq<T>,
    tracked Hlb1: &⟦mlist_ptsto_lb⟧<K,T>,
    tracked Hlb2: &⟦mlist_ptsto_lb⟧<K,T>,
)
requires
  holds(*Hlb1, ⟨mlist_ptsto_lb⟩(γ, k, l)),
  holds(*Hlb2, ⟨mlist_ptsto_lb⟩(γ, k, l_p)),
ensures
  l.is_prefix_of(l_p) || l_p.is_prefix_of(l)
{
    unimplemented!()
}


#[verifier(external_body)]
proof fn mlist_ptsto_update<K,T>(
    γ:gname, k:K, l:Seq<T>, l_p:Seq<T>,
    tracked Hptsto: ⟦mlist_ptsto⟧<K,T>,
) -> (tracked Hout:⟦mlist_ptsto⟧<K,T>)
requires
  l.is_prefix_of(l_p),
  holds(Hptsto, ⟨mlist_ptsto⟩(γ, k, l)),
ensures
  holds(Hout, ⟨mlist_ptsto⟩(γ, k, l_p)),
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
    γ:gname, k:K, l:Seq<T>, l_p:Seq<T>,
    tracked Hptsto: &⟦mlist_ptsto_lb⟧<K,T>,
) -> (tracked Hout:⟦mlist_ptsto_lb⟧<K,T>)
requires
  l_p.is_prefix_of(l),
  holds(*Hptsto, ⟨mlist_ptsto_lb⟩(γ, k, l)),
ensures
  holds(Hout, ⟨mlist_ptsto_lb⟩(γ, k, l_p)),
{
    unimplemented!()
}

#[verifier(external_body)]
proof fn mlist_ptsto_half_combine<K,T>(
    γ:gname, k:K, l1:Seq<T>, l2:Seq<T>,
    tracked Hptsto1: ⟦mlist_ptsto_half⟧<K,T>,
    tracked Hptsto2: ⟦mlist_ptsto_half⟧<K,T>,
) -> (tracked Hptsto:⟦mlist_ptsto⟧<K,T>)
requires
  holds(Hptsto1, ⟨mlist_ptsto_half⟩(γ, k, l1)),
  holds(Hptsto2, ⟨mlist_ptsto_half⟩(γ, k, l2)),
ensures
  l1 == l2,
  holds(Hptsto, ⟨mlist_ptsto⟩(γ, k, l1)),
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
    γ:gname, k:K, l:Seq<T>,
    tracked Hptsto: &⟦mlist_ptsto_half⟧<K,T>,
) -> (tracked Hout:⟦mlist_ptsto_lb⟧<K,T>)
requires
  holds(*Hptsto, ⟨mlist_ptsto_half⟩(γ, k, l)),
ensures
  holds(Hout, ⟨mlist_ptsto_lb⟩(γ, k, l)),
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


#[verifier::reject_recursive_types(K)]
struct ⟦[∗ set]⟧<K, ⟦R⟧> {
    contents: Map<K, ⟦R⟧>
}
spec fn ⟨[∗ set]⟩<K, ⟦R⟧>(s:Set<K>, ⟨R⟩:spec_fn(K) -> spec_fn(⟦R⟧) -> bool)
                           -> spec_fn(⟦[∗ set]⟧<K, ⟦R⟧>) -> bool {
    |res:⟦[∗ set]⟧<K, ⟦R⟧>| {
        &&& res.contents.dom() =~= s
        &&& forall |k| s.contains(k) ==> ⟨R⟩(k)(#[trigger] res.contents[k])
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


type ⟦old_proposal_max⟧ =
    ⟦□⟧<⟦forall⟧<(u64, Seq<EntryType>),
        ⟦wand⟧<Pure, 
            ⟦wand⟧<⟦is_committed_by⟧, Pure>>>>;
spec fn ⟨old_proposal_max⟩(config:Set<mp_server_names>, γsys:mp_system_names, epoch:u64, σ:Seq<EntryType>)
    -> spec_fn(⟦old_proposal_max⟧) -> bool {
    ⟨□⟩(
    ⟨∀⟩(|f:(u64,Seq<EntryType>)| {
            let epoch_old = f.0;
            let σ_old = f.1;
            ⟨wand⟩(
              |_p| epoch_old < epoch,
              ⟨wand⟩(
                ⟨is_committed_by⟩(config, epoch_old, σ_old),
                |_p| σ_old.is_prefix_of(σ)))
        }
    )
    )
}

spec const ⊤ : Namespace = Set::new(|_p| true);
spec const replN : Name = 1;
// FIXME: need fupd_wand here
type ⟦is_proposal_valid⟧ =
⟦□⟧<⟦∀⟧<Seq<EntryType>,
        ⟦wand⟧<Pure, ⟦wand⟧<⟦own_commit⟧, ⟦fupd⟧<⟦own_commit⟧>>>
>>;
spec fn ⟨is_proposal_valid⟩(γsys:mp_system_names, σ:Seq<EntryType>)
    -> spec_fn(⟦is_proposal_valid⟧) -> bool {
    ⟨□⟩(
    ⟨∀⟩(|σ_p:Seq<EntryType>| {
      ⟨wand⟩(|_p| σ_p.is_prefix_of(σ),
             ⟨wand⟩(⟨own_commit⟩(γsys, σ_p),
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
⟦sep⟧<Pure,
  ⟦sep⟧<
    ⟦is_accepted_ro⟧,
    ⟦□⟧<⟦forall⟧<u64, ⟦wand⟧<Pure, ⟦wand⟧<Pure, ⟦is_accepted_ro⟧>>>>,
>>;
#[verifier::opaque]
closed spec fn logPrefixTrigger(logPrefix:Seq<EntryType>) -> bool {
    true
}
spec fn ⟨is_accepted_upper_bound⟩(γsrv:mp_server_names, log:Seq<EntryType>, acceptedEpoch:u64, newEpoch:u64)
                                  -> spec_fn(⟦is_accepted_upper_bound⟧) -> bool
{
    |res| {
        exists |logPrefix:Seq<EntryType>| {
        &&& #[trigger] logPrefixTrigger(logPrefix)
        &&& ⟨sep⟩(
        |_p| { logPrefix.is_prefix_of(log) },
        ⟨sep⟩(
        ⟨is_accepted_ro⟩(γsrv, acceptedEpoch, logPrefix),
        ⟨□⟩(⟨forall⟩(|epoch_p:u64| {
            ⟨wand⟩(
                |_p| acceptedEpoch < epoch_p,
                ⟨wand⟩(
                    |_x| epoch_p < newEpoch,
                    ⟨is_accepted_ro⟩(γsrv, epoch_p, Seq::empty())
                )
            )}))))(res)
        }
    }
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
        holds(res.HepochIneq, |_p| st.accepted_epoch <= st.epoch) &&
        holds(res.Hacc, ⟨own_accepted⟩(γsrv, st.epoch, if (st.accepted_epoch == st.epoch) {
                    st.log
                } else {
                    Seq::empty()
                })) &&
        holds(res.Hacc_ub, ⟨or⟩(
            |_p| !(st.accepted_epoch < st.epoch),
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
    mlist_ptsto_lb_mono(γsrv.accepted_gn, st.accepted_epoch, st.log, st.log, &Hown.Hacc_lb)
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
    mlist_ptsto_lb_comparable(γsys.proposal_gn, epoch_p, st.log, log_p,
                               &Hown.Hprop_lb, &Hprop_lb);
    // assert(st.log.is_prefix_of(log_p));
    Hown.Hacc = mlist_ptsto_update(γsrv.accepted_gn, epoch_p, st.log, log_p, Hown.Hacc);
    Hown.Hacc_lb = mlist_ptsto_get_lb(γsrv.accepted_gn, epoch_p, log_p, &Hown.Hacc);
    Hown.Hprop_lb = Hprop_lb;
    Hown.Hprop_facts = Hprop_facts;
    Hown
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
    mlist_ptsto_lb_comparable(γsys.proposal_gn, epoch_p, st.log, log_p,
                               &Hown.Hprop_lb, &Hprop_lb);
    mlist_ptsto_lb_mono(γsrv.accepted_gn, st.accepted_epoch, st.log, log_p, &Hown.Hacc_lb)
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
    let tracked mut Hown = Hown;
    let st_p = MPaxosState{epoch:epoch_p, accepted_epoch:epoch_p, log:log_p};
    Hown.Hprop_lb = Hprop_lb;
    Hown.Hprop_facts = Hprop_facts;
    Hown.Hacc_ub = ⟦or⟧::Left(());
    if st.epoch < epoch_p {
        Hown.Hunused.contents.tracked_remove_keys(Set::new(|e:u64| st.epoch < e < st_p.epoch));
        let tracked mut Hacc = Hown.Hunused.contents.tracked_remove(epoch_p);
        Hacc = mlist_ptsto_update(γsrv.accepted_gn, epoch_p, Seq::empty(), log_p, Hacc);
        let tracked Hacc_lb = mlist_ptsto_get_lb(γsrv.accepted_gn, epoch_p, log_p, &Hacc);
        Hown.Hvotes.contents.tracked_remove_keys(Set::new(|e:u64| st.epoch < e < st_p.epoch));
        Hown.Hvotes.contents.tracked_remove(st_p.epoch);
        Hown.Hacc = Hacc;
        Hown.Hacc_lb = Hacc_lb;
        return Hown;
    } else if st.epoch == epoch_p {
        let tracked mut Hacc = mlist_ptsto_update(γsrv.accepted_gn, epoch_p, Seq::empty(), log_p, Hown.Hacc);
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
    old(E)@ =~= Set::new(|_p| true),
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
            Hown.Hprop_facts.0.dup().instantiate((epoch, σ))
            .instantiate(())
            .instantiate(Hcom);
            assert(σ.is_prefix_of(σcommit)); // right
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
        let tracked Hprop_valid = Hprop_facts.1.dup();
        let tracked Hcommit = Hprop_valid.instantiate(σcommit).
            instantiate(()).
            instantiate(Hown.Hcommit).
            elim(E);
        let tracked Hlb = mlist_ptsto_half_get_lb(γsys.state_gn, 0, σ, &Hcommit);

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
        let tracked Hlb = mlist_ptsto_half_get_lb(γsys.state_gn, 0, σcommit, &Hown.Hcommit);
        let tracked Hlb = mlist_ptsto_lb_mono(γsys.state_gn, 0, σcommit, σ, &Hlb);
        // close invariant
        let tracked Hown = ⟦∃⟧::exists((σcommit, epoch_commit), Hown);
        inv_close(replN, ⟨is_repl_inv_inner⟩(config, γsys), E, Hown, Hclose);
        return Hlb;
    } else {
        assert(false);
        return false_to_anything();
    }
}

fn main() {}
}
