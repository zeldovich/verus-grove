#![verifier::loop_isolation(false)]
#![allow(non_camel_case_types)]
use vstd::{prelude::*};
use vstd::{set_lib::*};
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

type EnterNewEpochArgs = u64;
struct EnterNewEpochReply {
    err: u64,
    accepted_epoch: u64,
    next_index: u64,
    state: StateType,
}

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

    fn enter_new_epoch(&self, args:EnterNewEpochArgs) -> (ret:EnterNewEpochReply)
        requires self.inv()
    {
        let (mut s, mut res) = self.mu.lock();
        let mut reply = EnterNewEpochReply{
            err: EEpochStale,
            accepted_epoch: 0,
            next_index: 0,
            state: 0,
        };
        if s.epoch >= args {
            self.mu.unlock((s, res));
            return reply;
        }
        s.epoch = args;
        reply.accepted_epoch = s.accepted_epoch;
        reply.next_index = s.next_index;
        reply.state = s.state;
        self.mu.unlock((s, res));
        return reply;
    }
}

////////////////////////////////////////////////////////////////////////////////
// Proposer

struct ProposerState {
    epoch : u64,
    next_index : u64,
    state : StateType,

    is_leader : bool,
    clerks : &'static Vec<&'static Acceptor>,
}

pub struct Proposer {
    mu: lock::Lock<(ProposerState, Tracked<()>)>,
}

pub struct Committer<'a> {
    s: ProposerState,
    res: Tracked<()>,
    p: &'a Proposer
}

impl Proposer {
    spec fn inv(self) -> bool {
        forall |s| #[trigger] self.mu.get_pred()(s) <==> true
    }

    fn start<'a>(&'a self) -> (r:(u64, Committer<'a>))
        requires self.inv()
        ensures r.1.inv(r.0)
    {
        let (mut s, mut res) = self.mu.lock();
        return (s.state, Committer {
            s: s,
            res: res,
            p: self,
        });
    }


    fn try_become_leader(&self)
        requires self.inv()
    {
        let (mut s, mut res) = self.mu.lock();
        if s.is_leader {
            self.mu.unlock((s, res));
            return
        }

        let mut num_successes = 0u64;
        assume((s.next_index as nat) < u64::MAX);
        s.epoch = s.epoch + 1;
        s.is_leader = false;
        let args = s.epoch;
        let clerks = s.clerks;
        self.mu.unlock((s, res));

        let mut i : usize = 0;

        let ghost config = self.config;
        let mut latest_reply = EnterNewEpochReply{
            err: 1,
            accepted_epoch: 0,
            next_index: 0,
            state: 0,
        };
        while i < NUM_REPLICAS as usize
            invariant
              0 <= i <= NUM_REPLICAS,
              0 <= num_successes <= i,
        {
            let reply = clerks[i].enter_new_epoch(args);
            if reply.err == ENone {
                num_successes += 1;
                if latest_reply.err != 0 {
                    latest_reply = reply
                } else if
                    latest_reply.accepted_epoch < reply.accepted_epoch {
                    latest_reply = reply
                } else if latest_reply.accepted_epoch == reply.accepted_epoch &&
                    latest_reply.next_index < reply.next_index {
                    latest_reply = reply
                }
            }
            i += 1;
        }

        if 2*num_successes > NUM_REPLICAS {
            // have a quorum
            let (mut s, mut res) = self.mu.lock();
            if s.epoch <= args.epoch {
                s.epoch = args.epoch;
                s.is_leader = true;
                s.next_index = latest_reply.next_index;
                s.state = latest_reply.state;
            }
            self.mu.unlock((s, res));
        }
    }
}

impl<'a> Committer<'a> {
    spec fn inv(self, oldState:u64) -> bool {
        true
    }

    fn try_commit_internal(self, newState:StateType) -> Error
        requires
          self.inv(oldState@),
    {
        let mut s = self.s;
        let mut res = self.res;
        if !s.is_leader {
            self.p.mu.unlock((s, res));
            return (ENotLeader, Tracked(⟦∨⟧::Left(Pure{})));
        }

        let mut num_successes = 0u64;
        assume((s.next_index as nat) < u64::MAX);
        s.next_index = s.next_index + 1;
        s.state = newState;
        let args = AcceptorApplyArgs{
            epoch: s.epoch,
            next_index: s.next_index,
            state: newState,
        };
        let clerks = s.clerks;

        let mut i : usize = 0;

        let ghost config = self.p.config;
        while i < NUM_REPLICAS as usize
            invariant
              0 <= i <= NUM_REPLICAS,
              0 <= num_successes <= i,
        {
            let reply = clerks[i].apply(args, Tracked(Hrpc_pre.dup()));
            if reply == ENone {
                num_successes += 1;
            }
            i += 1;
        }

        if 2*num_successes > NUM_REPLICAS {
            // have a quorum
            return ENone;
        }
        return (EEpochStale, Tracked(⟦∨⟧::Left(Pure{})));
    }
}
