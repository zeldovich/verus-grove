use vstd::{prelude::*,invariant::*,thread::*};
// use std::sync::Arc;
mod lock;
mod kv;
// mod lmap;
use kv::*;

verus! {
    struct KvErpcState {
        kv:KvState,
        replies:lmap::LMap<u64,u64>, //<u64>,
        nextFreshReqId:u64,
    }

    struct KvErpcServer {
        s: lock::Lock<KvErpcState>,
        pub id: Ghost<nat>,
        pub tok_gnames: Ghost<Map<u64,nat>>,
    }

    // fn contains(v:&Vec<u64>, k:u64) -> (ret:bool)
    //     ensures ret == v@.contains(k)
    // {
    //     let mut i = 0;
    //     while i < v.len()
    //         invariant i <= v.len(),
    //                   !v@.subrange(0,i as int).contains(k),
    //     {
    //         if v[i] == k {
    //             return true;
    //         }
    //         i += 1;
    //         proof { lemma_seq_properties::<u64>(); }
    //         // assert(forall|j:int| 0 <= j < v@.len() ==> v@[j] != k);
    //         // assert (!v@.subrange(0,i as int).contains(k))
    //     }
    //     proof { lemma_seq_skip_nothing(v@, 0); }
    //     // assert(v@ == v@.subrange(0,i as int));
    //     return false;
    // }

    
    #[verifier(external_body)]
    pub struct GhostToken;

    #[verifier(external_body)]
    pub struct GhostWitness;

    impl GhostToken {
        spec fn gname(&self) -> nat;
    }

    impl GhostWitness {
        spec fn gname(&self) -> nat;
    }

    #[verifier(external_body)]
    proof fn token_exlcusive(tracked a:&GhostToken, tracked b:&GhostToken)
        requires a.gname() == b.gname()
        ensures false
    {
    }

    #[verifier(external_body)]
    proof fn token_witness(tracked a:&GhostToken, tracked b:&GhostWitness)
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

    // Either GhostMapPointsTo or 
    type PutResources =
        Or<Tracked<GhostMapPointsTo<u64,u64>>,
           Tracked<GhostWitness>,
           >;

    pub struct PutInvConsts {
        pub map_gname: nat,
        pub k:u64,
        pub tok_gname:nat,
    }

    struct PutPredicate {}
    impl InvariantPredicate<PutInvConsts, PutResources> for PutPredicate {
        closed spec fn inv(c: PutInvConsts, r: PutResources) -> bool {
            match r {
                Or::Left(ptsto) => {
                    ptsto@.id == c.map_gname
                }
                Or::Right(wit) => {
                    wit@.gname() == c.tok_gname
                }
            }
        }
    }

    type PutPreCond = AtomicInvariant<PutInvConsts, PutResources, PutPredicate>;

    #[verifier(external_body)]
    proof fn todo(gname:nat) -> (tracked r:GhostToken)
        ensures r.gname() == gname
    {
        unimplemented!()
    }

    impl KvErpcServer {
        pub fn get(&self, reqId:u64, k:u64) -> u64 {
            let mut s = self.s.lock();
            match s.replies.get(reqId) {
                Some(resp) => {
                    return *resp;
                }
                None => {
                    s.replies.insert(reqId, 1);
                    // return s.kv.get(k);
                    return 37;
                }
            }
        }

        // Step 1: get ownership of the KV points-to from the user, but don't
        // give it back. This'll require "one-way" escrow.
        pub fn put(&self, reqId:u64, k:u64, v:u64, pre:PutPreCond)
            requires
            self.tok_gnames@.contains_key(reqId),
            pre.constant() == (PutInvConsts{
                map_gname: self.id@,
                tok_gname: self.tok_gnames@[reqId],
                k: k,
            })
        {
            let mut s = self.s.lock();
            match s.replies.get(reqId) {
                Some(_) => {},
                None => {
                    // get ownership of GhostTok
                    let tracked tok = todo(self.tok_gnames@[reqId]);
                   
                    // TODO: I think we want to do `match &mut res { ... }` but
                    // verus doesn't support that.
                    // open invariant, and get GhostMapPointsTo out of it.
                    let tracked mut my_ptsto;
                    open_atomic_invariant!(&pre => r => {
                        proof {
                            let tracked mut x = &r;
                            match x {
                                Or::Left(ptsto) => {
                                    // TODO: want to get ownership to the outer context.
                                    my_ptsto = ptsto;
                                }
                                Or::Right(wit) => {
                                    token_witness(&tok, wit.borrow());
                                    assert(false);
                                }
                            }
                        }
                    });

                    // s.kv.put(k,v,Tracked(my_ptsto.borrow_mut()));
                    s.replies.insert(k,0);
                }
            }
            return;
        }
    }

    fn main() {
    }
} // verus!
