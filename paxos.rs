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
enum Or<A,B> {Left(A), Right(B)}

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
spec fn ⟨mlist_ptsto⟩<K,T>(γ:gname, key:u64, l:Seq<T>) -> spec_fn(⟦mlist_ptsto⟧<K,T>) -> bool;


#[verifier(external_body)]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(T)]
struct ⟦mlist_ptsto_lb⟧<K,T> {
    _phantom1 : std::marker::PhantomData<K>,
    _phantom2 : std::marker::PhantomData<T>,
}
spec fn ⟨mlist_ptsto_lb⟩<K,T>(γ:gname, key:u64, l:Seq<T>) -> spec_fn(⟦mlist_ptsto_lb⟧<K,T>) -> bool;

                 
#[verifier(external_body)]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(T)]
struct ⟦mlist_ptsto_ro⟧<K,T> {
    _phantom1 : std::marker::PhantomData<K>,
    _phantom2 : std::marker::PhantomData<T>,
}
spec fn ⟨mlist_ptsto_ro⟩<K,T>(γ:gname, key:u64, l:Seq<T>) -> spec_fn(⟦mlist_ptsto_ro⟧<K,T>) -> bool;

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
type ⟦is_proposal_facts⟧ = ⟦mlist_ptsto_lb⟧<u64, EntryType>; // FIXME: wrong type
type ⟦is_accepted_lb⟧ = ⟦mlist_ptsto_lb⟧<u64, EntryType>;
type ⟦own_accepted⟧ = ⟦mlist_ptsto⟧<u64, EntryType>;

type ⟦is_accepted_ro⟧ = ⟦mlist_ptsto_ro⟧<u64, EntryType>;
spec fn ⟨is_accepted_ro⟩(γsrv:mp_server_names, epoch:u64, l:Seq<EntryType>) ->
            spec_fn(⟦is_accepted_ro⟧) -> bool
{
    |res| {
        ⟨mlist_ptsto_ro⟩(γsrv.accepted_gn, epoch, l)(res)
    }
}


type ⟦own_vote_tok⟧ = ⟦tok_points_to⟧;
spec fn ⟨own_vote_tok⟩(γsrv:mp_server_names, epoch:u64) -> spec_fn(⟦own_vote_tok⟧) -> bool {
    |res| {
        ⟨tok_points_to⟩(γsrv.vote_gn, epoch)(res)
    }
}

type ⟦is_accepted_upper_bound⟧ = (
    ⟦is_accepted_ro⟧,
    ⟦□⟧<⟦forall⟧<u64, ⟦wand⟧<Pure, ⟦wand⟧<Pure, ⟦is_accepted_ro⟧>>>>,
);
closed spec fn logPrefixTrigger(logPrefix:Seq<EntryType>) -> bool {
    true
}
spec fn ⟨is_accepted_upper_bound⟩(γsrv:mp_server_names, log:Seq<EntryType>, acceptedEpoch:u64, newEpoch:u64)
                                  -> spec_fn(⟦is_accepted_upper_bound⟧) -> bool
{
    |res:⟦is_accepted_upper_bound⟧| {
        exists |logPrefix:Seq<EntryType>| {
            &&& #[trigger] logPrefixTrigger(logPrefix)
            &&& logPrefix.is_prefix_of(log)
            &&& ⟨is_accepted_ro⟩(γsrv, acceptedEpoch, logPrefix)(res.0)
            &&& ⟨□⟩(
                ⟨forall⟩(|epoch_p:u64| {
                ⟨wand⟩(
                    |_x| acceptedEpoch < epoch_p,
                    ⟨wand⟩(
                        |_x| epoch_p < newEpoch,
                        ⟨is_accepted_ro⟩(γsrv, epoch_p, Seq::empty())
                    )
                )}))(res.1)
        }
    }
}


struct ⟦own_replica_ghost⟧ {
    Hprop_lb : ⟦is_proposal_lb⟧,
    Hprop_facts : ⟦is_proposal_facts⟧,
    Hacc_lb : ⟦is_accepted_lb⟧,
    HepochIneq : Pure,
    Hacc : ⟦own_accepted⟧,
    Hacc_ub : Or<True, ⟦is_accepted_upper_bound⟧>,
    Hunused : ⟦big_sepS⟧<u64, ⟦own_accepted⟧>,
    Hvotes : ⟦big_sepS⟧<u64, ⟦own_vote_tok⟧>,
}
    
fn main() {}
}
