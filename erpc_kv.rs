#![allow(mixed_script_confusables)]
#![deny(non_ascii_idents)]

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

    // XXX: what's the meaning of the `ghost` keyword here? Inferring that it's
    // the same as making each field be a `ghost` field, but not sure.
    pub ghost struct ExactlyOnceGnames {
        pub req_gnames: Map<u64,nat>,
        pub reply_gnames: Map<u64,nat>,
    }

    // TODO: make a bundle of gnames, so that we can introduce separate types for each of
    // these CSL props, that each take a gname-bundle as input (really, keeping
    // it as a field).
    // TODO: is it possible to actually pass in the gname as an input parameter?
    // E.g. want to write GhostToken<gname> or GhostToken(gname) or maybe even
    // (t : GhostToken)?
    // (Unexecuted ∗ k ↦ x ∨ Executed ∗ ServerCompleted ∗ (k ↦ v ∨ ClientClaimed))
    type PutResources =
        Tracked<Or<(GhostToken, GhostMapPointsTo<u64,u64>),
           (GhostWitness, // Executed
            GhostWitness, // ServerCompleted
            Or<GhostMapPointsTo<u64,u64>, GhostWitness,>),>>;

    pub struct PutInvConsts {
        pub k:u64,
        pub v:u64,
        pub req_id:u64,
        pub kv_gname: nat,
        pub gamma:ExactlyOnceGnames,
    }

    struct PutPredicate {}
    impl InvariantPredicate<PutInvConsts, PutResources> for PutPredicate {
        closed spec fn inv(c: PutInvConsts, r: PutResources) -> bool {
            c.gamma.req_gnames.contains_key(c.req_id) && // XXX(total map)
            c.gamma.reply_gnames.contains_key(c.req_id) && // XXX(total map)
            match r@ {
                Or::Left((unexecuted, ptsto)) => {
                    unexecuted.gname() == c.gamma.req_gnames[c.req_id] &&
                    ptsto.gname() == c.kv_gname &&
                    ptsto.k == c.k
                }
                Or::Right((executed, receipt, client_escrow)) => {
                    executed.gname() == c.gamma.req_gnames[c.req_id] &&
                    receipt.gname() == c.gamma.reply_gnames[c.req_id]  &&
                    match client_escrow {
                        Or::Left(ptsto) => {
                            ptsto.gname() == c.kv_gname
                            // FIXME: more stuff here about k and v 
                        }
                        Or::Right(claimed) => {
                            claimed.gname() == c.gamma.req_gnames[c.req_id]
                        }
                    }
                }
            }
        }
    }

    type PutPreCond = AtomicInvariant<PutInvConsts, PutResources, PutPredicate>;

    #[verifier(external_body)]
    proof fn false_to_anything<A>() -> (tracked r:Tracked<A>)
        requires false
    {
        unimplemented!();
    }

    struct KvErpcState {
        kv:KvState,
        replies:lmap::LMap<u64,u64>,
        next_fresh_req_id:u64,
        client_toks: Tracked<Map<u64,GhostToken>>, // this is a big_sepM
        server_toks: Tracked<Map<u64,GhostToken>>,
    }

    struct KvErpcServer {
        s: lock::Lock<KvErpcState>,
        pub kv_gname: Ghost<nat>,
        pub gamma:Ghost<ExactlyOnceGnames>,
    }

    spec fn lockPredGen(s:KvErpcServer) -> FnSpec(KvErpcState) -> bool {
        |st:KvErpcState|
        st.kv.gname() == s.kv_gname &&
            st.kv.kv_inv() &&
            // own all client-side tokens with req_id >= next_fresh_req_id, and they all have
            // the right gnames.

            // FIXME: need to figure out the right trigger to pick, makes a big
            // difference.
            (forall |req_id:u64| req_id >= st.next_fresh_req_id ==>
             #[trigger] 
             st.client_toks@.contains_key(req_id) &&
             s.gamma@.req_gnames.contains_key(req_id) &&
             st.client_toks@[req_id].gname() == s.gamma@.req_gnames[req_id]
            ) &&
            (forall |req_id:u64| !(#[trigger] st.replies@.contains_key(req_id)) ==>
             st.server_toks@.contains_key(req_id) &&
             s.gamma@.reply_gnames.contains_key(req_id) &&
             st.server_toks@[req_id].gname() == s.gamma@.reply_gnames[req_id]
            )
    }

    impl KvErpcServer {
        pub closed spec fn inv(self) -> bool {
            self.s.getPred() == lockPredGen(self)
        }

        proof fn put_fupd(&self, tok:GhostToken, pre:&PutPreCond, tracked ghostMap:&mut GhostMapAuth<u64,u64>)
                          -> (tracked r:GhostWitness)
            requires self.gamma@.reply_gnames.contains_key(pre.constant().req_id), // XXX(total map)
            tok.gname() == self.gamma@.reply_gnames[pre.constant().req_id],
            pre.constant().kv_gname == old(ghostMap).gname(),

            ensures old(ghostMap).gname() == ghostMap.gname(),
            // ghostMap.kvs == old(ghostMap).insert(pre.k, )
            
        {
            assume(false);
            false_to_anything().get()
        }

        // Step 1: get ownership of the KV points-to from the user, but don't
        // give it back. This'll require "one-way" escrow.
        #[verifier(external_body)]
        pub fn put(&self, req_id:u64, k:u64, v:u64, pre:&PutPreCond)
            requires
            self.inv(),
            self.gamma@.reply_gnames.contains_key(req_id),
            pre.constant() == (PutInvConsts{
                kv_gname: self.kv_gname@,
                req_id: req_id,
                k: k,
                v: v,
                gamma: self.gamma@,
            })
        {
            /*
            let mut s = self.s.lock();
            match s.replies.get(req_id) {
                Some(_) => {},
                None => {
                    // get ownership of GhostTok
                    let tracked tok;
                    proof {
                        assert(!s.replies@.contains_key(req_id));
                        assert(s.server_toks@.contains_key(req_id));
                        tok = (s.server_toks.borrow_mut()).tracked_remove(req_id);
                    }
                   
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
                                    ptsto = Tracked(false_to_anything()).get();
                                    r = Or::Right(wit);
                                }
                            }
                        }
                    });

                    s.kv.put(k,v,Tracked(ptsto.borrow_mut()));
                    s.replies.insert(req_id,0);
                    // NOTE(test): commenting this out makes the proof fail. Neat!
                }
            }
            proof {
                // assert(s.kv.get_id() == self.id);
                // assert(s.kv.kv_inv());

                // assert (forall |req_id:u64| req_id >= s.next_fresh_req_id ==>
                //         #[trigger] 
                //  s.client_toks@.contains_key(req_id) &&
                //  self.gamma@.req_gnames.contains_key(req_id) &&
                //  s.client_toks@[req_id].gname() == self.gamma@.req_gnames[req_id]
                // );

                // assert (forall |req_id:u64| !(#[trigger] s.replies@.contains_key(req_id)) ==>
                //  s.server_toks@.contains_key(req_id) &&
                //  self.gamma@.reply_gnames.contains_key(req_id) &&
                //  s.server_toks@[req_id].gname() == self.gamma@.reply_gnames[req_id]
                // );
                // assert(lockPredGen(*self)(s));
            }
            self.s.unlock(s);
             */
            return;
        }

        pub fn get(&self, req_id:u64, k:u64) -> u64 {
            let mut s = self.s.lock();
            match s.replies.get(req_id) {
                Some(resp) => {
                    return *resp;
                }
                None => {
                    s.replies.insert(req_id, 1);
                    // return s.kv.get(k);
                    return 37;
                }
            }
        }
    }

    fn main() {
    }
} // verus!
