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
type ⟦sep⟧<⟦P⟧,⟦Q⟧> = (⟦P⟧, ⟦Q⟧);
spec fn ⟨sep⟩<⟦P⟧,⟦Q⟧>(⟨P⟩:spec_fn(⟦P⟧) -> bool, ⟨Q⟩:spec_fn(⟦Q⟧) -> bool)
    -> spec_fn(⟦sep⟧<⟦P⟧,⟦Q⟧>) -> bool {
    |res:⟦sep⟧<_,_>| {
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

    proof fn instantiate(tracked self, i:P) -> (out:Q) where Self: std::marker::Sized
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
    proof fn instantiate(tracked self, i:⟦P⟧) -> (out:⟦Q⟧) {
        unimplemented!();
    }
}
impl<⟦P⟧, ⟦Q⟧> ⟦wand⟧<⟦P⟧, ⟦Q⟧> {
    #[verifier(external_body)]
    fn from<T:wand_tr<⟦P⟧,⟦Q⟧>>(x:T) -> (r:Self)
        ensures r.pre() == x.pre(),
        r.post() == x.post(),
    {
        unimplemented!();
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

    proof fn instantiate(self, x:X) -> (out:⟦A⟧) where Self: std::marker::Sized
        ensures self.post()(x)(out)
    ;
}

/// model for dyn forall_tr
#[verifier(external_body)]
#[verifier::reject_recursive_types(X)]
#[verifier::reject_recursive_types(⟦A⟧)]
struct ⟦forall⟧<X,⟦A⟧> {
    _phantom : std::marker::PhantomData<(X,⟦A⟧)>,
}
impl<X,⟦A⟧> forall_tr<X,⟦A⟧> for ⟦forall⟧<X,⟦A⟧> {
    spec fn post(&self) -> spec_fn(x:X) -> spec_fn(out:⟦A⟧) -> bool;

    #[verifier(external_body)]
    proof fn instantiate(self, x:X) -> (out:⟦A⟧) where Self: std::marker::Sized {
        unimplemented!();
    }
}
spec fn ⟨forall⟩<X,⟦A⟧>(⟨A⟩:spec_fn(x:X) -> spec_fn(out:⟦A⟧) -> bool)
    -> spec_fn(⟦forall⟧<X,⟦A⟧>) -> bool
{
    |res:⟦forall⟧<_,_>| {
        res.post() == ⟨A⟩
    }
}


/// □ P
trait □_tr<⟦P⟧> {
    spec fn post(&self) -> spec_fn(out:⟦P⟧) -> bool;

    proof fn dup(&self) -> (out:⟦P⟧)
        ensures self.post()(out)
        opens_invariants none
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
    proof fn dup(&self) -> (out:⟦P⟧) {
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
proof fn mlist_ptsto_lb_comparable<K,T>(
    γ:gname, k:K, l:Seq<T>, l_p:Seq<T>,
    Hlb1: ⟦mlist_ptsto_lb⟧<K,T>,
    Hlb2: ⟦mlist_ptsto_lb⟧<K,T>,
)
requires
  holds(Hlb1, ⟨mlist_ptsto_lb⟩(γ, k, l)),
  holds(Hlb2, ⟨mlist_ptsto_lb⟩(γ, k, l_p)),
ensures
  l.is_prefix_of(l_p) || l_p.is_prefix_of(l)
{
    unimplemented!()
}


#[verifier(external_body)]
proof fn mlist_ptsto_update<K,T>(
    γ:gname, k:K, l:Seq<T>, l_p:Seq<T>,
    Hptsto: ⟦mlist_ptsto⟧<K,T>,
) -> (Hout:⟦mlist_ptsto⟧<K,T>)
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
    Hptsto: &⟦mlist_ptsto⟧<K,T>,
) -> (Hout:⟦mlist_ptsto_lb⟧<K,T>)
requires
  holds(*Hptsto, ⟨mlist_ptsto⟩(γ, k, l)),
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
struct ⟦big_sepS⟧<K, ⟦R⟧> {
    contents: Map<K, ⟦R⟧>
}
spec fn ⟨big_sepS⟩<K, ⟦R⟧>(s:Set<K>, ⟨R⟩:spec_fn(K) -> spec_fn(⟦R⟧) -> bool)
                           -> spec_fn(⟦big_sepS⟧<K, ⟦R⟧>) -> bool {
    |res:⟦big_sepS⟧<K, ⟦R⟧>| {
        &&& res.contents.dom() == s
        &&& forall |k| #[trigger] s.contains(k) ==> ⟨R⟩(k)(res.contents[k])
    }
}


type EntryType = StateType;
type ⟦is_proposal_lb⟧ = ⟦mlist_ptsto_lb⟧<u64, EntryType>;
spec fn ⟨is_proposal_lb⟩(γsys:mp_system_names, epoch:u64, σ:Seq<EntryType>) ->
    spec_fn(⟦is_proposal_lb⟧) -> bool
{
    ⟨mlist_ptsto_lb⟩(γsys.proposal_gn, epoch, σ)
}

// FIXME: wrong prop
type ⟦is_proposal_facts⟧ = ⟦mlist_ptsto_lb⟧<u64, EntryType>; 
spec fn ⟨is_proposal_facts⟩(γsys:mp_system_names, epoch:u64, σ:Seq<EntryType>) ->
    spec_fn(⟦is_proposal_facts⟧) -> bool
{
    ⟨mlist_ptsto_lb⟩(γsys.proposal_gn, epoch, σ)
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


type ⟦own_vote_tok⟧ = ⟦tok_points_to⟧;
spec fn ⟨own_vote_tok⟩(γsrv:mp_server_names, epoch:u64) -> spec_fn(⟦own_vote_tok⟧) -> bool {
    |res| {
        ⟨tok_points_to⟩(γsrv.vote_gn, epoch)(res)
    }
}

type ⟦is_accepted_upper_bound⟧ =
⟦sep⟧<Pure,
  ⟦sep⟧<
    ⟦is_accepted_ro⟧,
    ⟦□⟧<⟦forall⟧<u64, ⟦wand⟧<Pure, ⟦wand⟧<Pure, ⟦is_accepted_ro⟧>>>>,
>>;
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
    Hunused : ⟦big_sepS⟧<u64, ⟦own_accepted⟧>,
    Hvotes : ⟦big_sepS⟧<u64, ⟦own_vote_tok⟧>,
}

ghost struct MPaxosState {
    epoch : u64,
    accepted_epoch : u64,
    log : Seq<EntryType>,
}
spec fn ⟨own_replica_ghost⟩(γsys:mp_system_names, γsrv:mp_server_names, st:MPaxosState) 
    -> spec_fn(⟦own_replica_ghost⟧) -> bool {
    |res:⟦own_replica_ghost⟧| {
        holds(res.Hprop_lb, ⟨is_proposal_lb⟩(γsys, st.accepted_epoch, st.log)) &&
        holds(res.Hprop_facts, ⟨is_proposal_facts⟩(γsys, st.accepted_epoch, st.log)) &&
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
        holds(res.Hunused, ⟨big_sepS⟩(
            Set::new(|e:u64| e > st.epoch),
            |e| ⟨own_accepted⟩(γsrv, e, Seq::empty())
        )) &&
        holds(res.Hvotes, ⟨big_sepS⟩(
            Set::new(|e:u64| e > st.epoch),
            |e| ⟨own_vote_tok⟩(γsrv, e)
        ))
    }
}

proof fn ghost_replica_accept_same_epoch(
    γsys:mp_system_names,
    γsrv:mp_server_names,
    st:MPaxosState,
    epoch_p:u64,
    log_p: Seq<EntryType>,
    Hown: ⟦own_replica_ghost⟧,
    Hprop_lb: ⟦is_proposal_lb⟧,
    Hprop_facts: ⟦is_proposal_facts⟧,
) ->
(ret: ⟦own_replica_ghost⟧)
  requires
    st.epoch <= epoch_p,
    st.accepted_epoch == epoch_p,
    st.log.len() <= log_p.len(),
    holds(Hown, ⟨own_replica_ghost⟩(γsys, γsrv, st)),
    holds(Hprop_lb, ⟨is_proposal_lb⟩(γsys, epoch_p, log_p)),
    holds(Hprop_facts, ⟨is_proposal_facts⟩(γsys, epoch_p, log_p)),
  ensures
    st.epoch == epoch_p,
    ⟨own_replica_ghost⟩(γsys, γsrv, MPaxosState{epoch:epoch_p, accepted_epoch:epoch_p, log:log_p})(ret)
{
    let mut Hown = Hown;
    // assert (st.epoch == epoch_p);
    // assert (st.accepted_epoch == st.epoch);
    mlist_ptsto_lb_comparable(γsys.proposal_gn, epoch_p, st.log, log_p,
                               Hown.Hprop_lb, Hprop_lb);
    // assert(st.log.is_prefix_of(log_p));
    Hown.Hacc = mlist_ptsto_update(γsrv.accepted_gn, epoch_p, st.log, log_p, Hown.Hacc);
    Hown.Hacc_lb = mlist_ptsto_get_lb(γsrv.accepted_gn, epoch_p, log_p, &Hown.Hacc);
    Hown.Hprop_lb = Hprop_lb;
    Hown.Hprop_facts = Hprop_facts;
    Hown
}

fn main() {}
}
