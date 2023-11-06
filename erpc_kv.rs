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

    struct KvErpcGhostResources {
        kv_auth: GhostMapAuth<u64,u64>,
        client_toks: Map<u64,GhostToken>, // this is a big_sepM
        server_toks: Map<u64,GhostToken>,
    }

    struct KvErpcState {
        m:lmap::LMap<u64,u64>,
        replies:lmap::LMap<u64,u64>,
        next_fresh_req_id:u64,
        g: Tracked<KvErpcGhostResources>,
    }

    struct KvErpcServer {
        mu: lock::Lock<KvErpcState>,
        pub kv_gname: Ghost<nat>,
        pub gamma:Ghost<ExactlyOnceGnames>,
    }

    spec fn gen_lock_pred(s:KvErpcServer) -> FnSpec(KvErpcState) -> bool {
        |st:KvErpcState|
        st.g@.kv_auth.gname() == s.kv_gname &&
            st.g@.inv(s.gamma@, st@)
    }

    // Want this so we can pass this in and out of the put_fupd lemma.
    ghost struct KvErpcStateGhost {
        m: Map<u64,u64>,
        replies: Map<u64,u64>,
        next_fresh_req_id: u64,
    }
    impl KvErpcStateGhost {
        // next state transitions
        pub closed spec fn put(self, req_id:u64, k:u64, v:u64) -> KvErpcStateGhost {
            // this is a "spec fn" version of the exec code
            if self.replies.contains_key(req_id) {
                self
            } else {
                KvErpcStateGhost{
                    replies: self.replies.insert(req_id, 0u64),
                    m: self.m.insert(k,v),
                    next_fresh_req_id: self.next_fresh_req_id,
                }
            }
        }

        spec fn get_fresh_req_id(self, req_id:u64, k:u64, v:u64) -> (KvErpcStateGhost, u64) {
            // this is a "spec fn" version of the exec code
            ((KvErpcStateGhost{
                replies: self.replies,
                m: self.m,
                next_fresh_req_id: (self.next_fresh_req_id + 1u64) as u64,
            }), self.next_fresh_req_id)
        }
    }

    impl KvErpcGhostResources {
        pub closed spec fn inv(&self, gamma:ExactlyOnceGnames, st:KvErpcStateGhost) -> bool {
            // own all client-side tokens with req_id >= next_fresh_req_id, and they all have
            // the right gnames.
            // Might need to figure out the right trigger to pick, makes a big
            // difference.
            self.kv_auth.kvs == st.m && // FIXME: make this gauge-invariant

            (forall |req_id:u64| req_id >= st.next_fresh_req_id ==>
             #[trigger] 
             self.client_toks.contains_key(req_id) &&
             gamma.req_gnames.contains_key(req_id) &&
             self.client_toks[req_id].gname() == gamma.req_gnames[req_id]
            ) &&
            (forall |req_id:u64| !(#[trigger] st.replies.contains_key(req_id)) ==>
             self.server_toks.contains_key(req_id) &&
             gamma.reply_gnames.contains_key(req_id) &&
             self.server_toks[req_id].gname() == gamma.reply_gnames[req_id]
            )
        }

        proof fn put_fupd(tracked &mut self, st:KvErpcStateGhost,
                                  tracked pre:&PutPreCond) -> (tracked receipt:GhostWitness)
            requires old(self).inv(pre.constant().gamma, st),
            pre.constant().kv_gname == old(self).kv_auth.gname(),

            ensures
            self.kv_auth.gname() == old(self).kv_auth.gname(),
            pre.constant().gamma.reply_gnames.contains_key(pre.constant().req_id),
            receipt.gname() == pre.constant().gamma.reply_gnames[pre.constant().req_id],
            self.inv(pre.constant().gamma, st.put(pre.constant().req_id, pre.constant().k, pre.constant().v,)),

            opens_invariants any
        {
            let req_id = pre.constant().req_id;
            if st.replies.contains_key(pre.constant().req_id) {
                // TODO: maintain and then get witness from server resources
                assume(false);
                return false_to_anything().get();
            } else { // case: first time seeing request
                // get out token
                let tracked server_tok = (self.server_toks).tracked_remove(req_id);
                let tracked witness;
                // open invariant, and fire the fupd with the points-to
                open_atomic_invariant!(&pre => r => {
                    match r {
                        Or::Left((unexecuted, mut ptsto)) => {
                            self.kv_auth.update(pre.constant().v, &mut ptsto);

                            let tracked executed;
                            executed = token_freeze(unexecuted);

                            let tracked receipt;
                            receipt = token_freeze(server_tok);
                            witness = witness_clone(&receipt);

                            // re-establish invariant:
                            r = Or::Right((executed, receipt, Or::Left(ptsto)));
                        }
                        Or::Right((executed, receipt, b)) => {
                            token_witness_false(&server_tok, &receipt);
                            assert(false);
                            witness = witness_clone(&executed);
                            r = Or::Right((executed, receipt, b));
                            // TODO: this stuff is here so the rest of
                            // the the compiler doesn't complain in the
                            // rest of the code that "r is moved" and
                            // "my_ptsto may be uninitialized".
                        }
                    }
                });
                return witness;
            }
        }
    }

    impl View for KvErpcState {
        type V = KvErpcStateGhost;
        closed spec fn view(&self) -> KvErpcStateGhost {
            KvErpcStateGhost{
                m: self.m@,
                replies: self.replies@,
                next_fresh_req_id: self.next_fresh_req_id,
            }
        }
    }

    impl KvErpcServer {
        pub closed spec fn inv(self) -> bool {
            self.mu.get_pred() == gen_lock_pred(self)
        }

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
            let mut s = self.mu.lock();
            let tracked witness = (s.g.borrow_mut()).put_fupd(s@, &pre);
            match s.replies.get(req_id) {
                Some(_) => {},
                None => {
                    s.replies.insert(req_id,0);
                    s.m.insert(k,v); // NOTE(test): commenting this out makes the proof fail. Neat!
                }
            }
            self.mu.unlock(s);
            return Tracked(witness);
        }

        pub fn get(&self, req_id:u64, k:u64) -> u64 {
            let mut s = self.mu.lock();
            match s.replies.get(req_id) {
                Some(resp) => {
                    let x = *resp;
                    self.mu.unlock(s);
                    return x;
                }
                None => {
                    // FIXME:
                    // s.replies.insert(req_id, 1);
                    // return s.kv.get(k);
                    self.mu.unlock(s);
                    return 37;
                }
            }
        }
    }

    fn main() {
    }
} // verus!
