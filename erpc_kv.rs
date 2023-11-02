use vstd::{prelude::*,invariant::*,thread::*};
// use std::sync::Arc;
mod lock;
mod kv;
// mod lmap;
use kv::*;

verus! {
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

    enum Or<A,B> {
        Left(A),
        Right(B),
    }

    // TODO: make a bundle of gnames, so that we can introduce separate types for each of
    // these CSL props, that each take a gname-bundle as input (really, keeping
    // it as a field).
    // TODO: is it possible to actually pass in the gname as an input parameter?
    // E.g. want to write GhostToken<gname> or GhostToken(gname) or maybe even
    // (t : GhostToken)?
    // (Unexecuted ∗ k ↦ x ∨ Executed ∗ ServerCompleted ∗ (k ↦ v ∨ ClientClaimed))
    type PutErpcResources =
        Or<Tracked<(GhostToken, GhostMapPointsTo<u64,u64>)>,
           Tracked<(GhostWitness, // Executed
                    GhostWitness, // ServerCompleted
                    Or<GhostMapPointsTo<u64,u64>,
                       GhostToken,>)
                   >,
           >;

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
                    ptsto@.id == c.map_gname &&
                    ptsto@.k == c.k
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

    #[verifier(external_body)]
    proof fn false_pointsto() -> (tracked r:GhostMapPointsTo<u64,u64>)
        requires false
    {
        unimplemented!();
    }

    struct KvErpcState {
        kv:KvState,
        replies:lmap::LMap<u64,u64>,
        nextFreshReqId:u64,
        toks: Tracked<Map<u64,GhostToken>>, // this is a big_sepM
    }

    struct KvErpcServer {
        s: lock::Lock<KvErpcState>,
        pub id: Ghost<nat>,
        pub tok_gnames: Ghost<Map<u64,nat>>,
    }

    spec fn lockPredGen(s:KvErpcServer) -> FnSpec(KvErpcState) -> bool {
        |st:KvErpcState|
        st.kv.get_id() == s.id &&
            st.kv.kv_inv() &&
            // own all tokens with reqId >= nextFreshReqId, and they all have
            // the right gnames.
            (forall |reqId:u64| reqId >= st.nextFreshReqId ==>
             st.toks@.contains_key(reqId) &&
             s.tok_gnames@.contains_key(reqId) &&
             #[trigger] st.toks@[reqId].gname() == s.tok_gnames@[reqId]
            )
    }

    impl KvErpcServer {
        pub closed spec fn inv(self) -> bool {
            self.s.getPred() == lockPredGen(self)
        }

        // Step 1: get ownership of the KV points-to from the user, but don't
        // give it back. This'll require "one-way" escrow.
        pub fn put(&self, reqId:u64, k:u64, v:u64, pre:&PutPreCond)
            requires
            self.inv(),
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
                   
                    // open invariant, and get GhostMapPointsTo out of it.

                    let tracked mut ptsto;
                    open_atomic_invariant!(&pre => r => {
                        proof {
                            match r {
                                Or::Left(ptsto_in) => {
                                    ptsto = ptsto_in;
                                    // re-establish invariant:
                                    r = Or::Right(Tracked(token_freeze(tok)));
                                }
                                Or::Right(wit) => {
                                    token_witness_false(&tok, wit.borrow());
                                    assert(false);
                                    // TODO: this stuff is here so the rest of
                                    // the the compiler doesn't complain in the
                                    // rest of the code that "r is moved" and
                                    // "my_ptsto may be uninitialized".
                                    ptsto = Tracked(false_pointsto());
                                    r = Or::Right(wit);
                                }
                            }
                        }
                    });

                    s.kv.put(k,v,Tracked(ptsto.borrow_mut()));
                    s.replies.insert(k,0);
                }
            }
            return;
        }

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
    }

    fn main() {
    }
} // verus!
