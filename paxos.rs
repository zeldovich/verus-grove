use vstd::{prelude::*};
use std::vec::Vec;
mod lock;

verus! {

type StateType = u64;

struct PaxosState {
    epoch : u64,
    accepted_epoch : u64,
    next_index : u64,
    state : StateType,
    is_leader : bool,
}

struct ServerState {
    ps : PaxosState,
    clerks : Vec<&'static Clerk>,
}

// Want to be able to use this to call methods on the underlying server objects.
#[verifier(external_body)]
type Clerk = Server;

type PaxosResource = u64;

pub struct Server {
    mu: lock::Lock<(ServerState, Tracked<PaxosResource>)>,
}

#[derive(Clone, Copy)]
struct ApplyAsFollowerArgs {
    epoch:u64,
    next_index:u64,
    state:StateType,
}

type Error = u64;
type ApplyAsFollowerReply = u64;

const ENone : u64 = 0u64;
const EEpochStale : u64 = 1u64;
const ENotLeader : u64 = 2u64;

const NUM_REPLICAS : u64 = 37;

// FIXME: no way to make this work with circularity caused by Clerk = Server
spec fn server_inv(s:ServerState, res:PaxosResource) -> bool {
    forall |j| 0 <= j < s.clerks@.len() ==> s.clerks@[j].inv()
}

impl Server {
    spec fn inv(self) -> bool {
        forall |s| #[trigger] self.mu.get_pred()(s) <==> server_inv(s.0, s.1@)
    }

    fn apply_as_follower(&self, args:ApplyAsFollowerArgs) -> (ret:ApplyAsFollowerReply)
        requires self.inv()
    {
        let (mut s, mut res) = self.mu.lock();
        let mut reply : ApplyAsFollowerReply;

        if s.ps.epoch <= args.epoch {
            if s.ps.accepted_epoch == args.epoch {
                if s.ps.next_index < args.next_index {
                    s.ps.next_index = args.next_index;
                    s.ps.state = args.state;
                    reply = ENone;
                } else { // args.next_index < s.next_index
                    reply = ENone;
                }
            } else { // s.accepted_epoch < args.epoch, because s.accepted_epoch <= s.epoch <= args.epoch
                s.ps.accepted_epoch = args.epoch;
                s.ps.epoch = args.epoch;
                s.ps.state = args.state;
                s.ps.next_index = args.next_index;
                s.ps.is_leader = false;
                reply = ENone;
            }
        } else {
            reply = EEpochStale;
        }

        self.mu.unlock((s, res));
        return 0;
    }

    // TODO: take as input a "step" function
    fn try_apply(&self) -> Error {
        let (mut s, mut res) = self.mu.lock();
        if !s.ps.is_leader {
            self.mu.unlock((s, res));
            return ENotLeader;
        }

        let mut num_successes = 0u64;
        let args = ApplyAsFollowerArgs{
            epoch: s.ps.epoch,
            next_index: s.ps.next_index,
            state: s.ps.state,
        };

        let mut i : usize = 0;
        while i < NUM_REPLICAS as usize {
            i += 1;
            let reply = s.clerks[i].apply_as_follower(args);
            if reply == ENone {
                num_successes += 1;
            }
        }

        if 2*num_successes > NUM_REPLICAS {
            return ENone
        }
        return EEpochStale
    }

}

fn main() {}
}
