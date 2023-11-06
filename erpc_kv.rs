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
        pub spec fn gname(&self) -> nat;
    }

    impl GhostWitness {
        pub spec fn gname(&self) -> nat;
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
        Or<(GhostToken, GhostMapPointsTo<u64,u64>),
           (GhostWitness, // Executed
            GhostWitness, // ServerCompleted
            Or<GhostMapPointsTo<u64,u64>, GhostWitness,>),>;

    pub struct PutInvConsts {
        pub k:u64,
        pub v:u64,
        pub req_id:u64,
        pub kv_gname: nat,
        pub gamma:ExactlyOnceGnames,
    }

    struct PutPredicate {}
    impl InvariantPredicate<PutInvConsts, PutResources> for PutPredicate {
        open spec fn inv(c: PutInvConsts, r: PutResources) -> bool {
            c.gamma.req_gnames.contains_key(c.req_id) && // XXX(total map)
            c.gamma.reply_gnames.contains_key(c.req_id) && // XXX(total map)
            match r {
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
                            ptsto.gname() == c.kv_gname &&
                            ptsto.k == c.k &&
                            ptsto.v == c.v
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
        m:lmap::LMap<u64,u64>,
        replies:lmap::LMap<u64,u64>,
        next_fresh_req_id:u64,

        ghostKvs: Tracked<GhostMapAuth<u64,u64>>,
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
        st.ghostKvs@.gname() == s.kv_gname &&
            st.ghostKvs@.kvs == st.m@ && // FIXME: make this gauge-invariant

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

        // FIXME: this doesn't fully encapsulate the server-side fupd. The
        // server_tok should be entirely inside of here.
        proof fn put_fupd(tracked &self, tracked server_tok:GhostToken,
                          tracked pre:&PutPreCond, tracked ghostMap:&mut GhostMapAuth<u64,u64>)
                          -> (tracked r:GhostWitness)
            requires
            self.gamma@ == pre.constant().gamma,
            self.gamma@.reply_gnames.contains_key(pre.constant().req_id), // XXX(total map)
            server_tok.gname() == self.gamma@.reply_gnames[pre.constant().req_id],
            pre.constant().kv_gname == old(ghostMap).gname(),

            ensures old(ghostMap).gname() == ghostMap.gname(),
            ghostMap.kvs == old(ghostMap).kvs.insert(pre.constant().k, pre.constant().v),
            r.gname() == self.gamma@.reply_gnames[pre.constant().req_id],
        opens_invariants any
        {
            let tracked wit;
            // open invariant, and get GhostMapPointsTo out of it.
                assert(1 == 1);
            open_atomic_invariant!(&pre => r => {
                match r {
                    Or::Left((unexecuted, mut ptsto)) => {
                        ghostMap.update(pre.constant().v, &mut ptsto);

                        let tracked executed;
                        executed = token_freeze(unexecuted);

                        let tracked receipt;
                        receipt = token_freeze(server_tok);
                        wit = witness_clone(&receipt);

                        // re-establish invariant:
                        r = Or::Right((executed, receipt, Or::Left(ptsto)));
                        // let c = pre.constant();
                        // assert(receipt.gname() == c.gamma.reply_gnames[c.req_id]);
                        // assert(PutPredicate::inv(pre.constant(), r));
                    }
                    Or::Right((executed, receipt, b)) => {
                        token_witness_false(&server_tok, &receipt);
                        assert(false);
                        wit = witness_clone(&executed);
                        r = Or::Right((executed, receipt, b));
                        // TODO: this stuff is here so the rest of
                        // the the compiler doesn't complain in the
                        // rest of the code that "r is moved" and
                        // "my_ptsto may be uninitialized".
                        // ptsto = Tracked(false_to_anything()).get();
                        // r = Or::Right(wit);
                    }
                }
            });
            return wit;
        }

        #[verifier(external_body)]
        pub fn put(&self, req_id:u64, k:u64, v:u64, pre:&PutPreCond) -> (witness:Tracked<GhostWitness>)
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

            ensures witness@.gname() == self.gamma@.reply_gnames[req_id],
        {
            let mut s = self.s.lock();
            let witness;
            match s.replies.get(req_id) {
                Some(_) => {
                    witness = Tracked(todo!());
                    // FIXME: return witness
                },
                None => {
                    // get ownership of GhostTok
                    proof {
                        assert(!s.replies@.contains_key(req_id));
                        assert(s.server_toks@.contains_key(req_id));
                        let tok = (s.server_toks.borrow_mut()).tracked_remove(req_id);
                        witness = Tracked(self.put_fupd(tok, &pre, s.ghostKvs.borrow_mut()));
                    }

                    s.replies.insert(req_id,0);
                    // NOTE(test): commenting this out makes the proof fail. Neat!
                }
            }
            self.s.unlock(s);
            return witness;
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
