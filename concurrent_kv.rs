use vstd::{prelude::*,seq_lib::*,thread::*};
use std::sync::Arc;
mod lock;

verus! {
    pub struct GhostMapAuth<#[verifier::reject_recursive_types] K,V> {
        id:nat,
        kvs:Map<K,V>,
    }

    pub struct GhostMapPointsTo<K,V> {
        id:nat,
        k:K,
        v:V,
    }

    impl<K,V> GhostMapAuth<K,V> {
        #[verifier(external_body)]
        proof fn agree(tracked &self, tracked ptsto:&GhostMapPointsTo<K,V>)
            requires ptsto.id == self.id
            ensures
                self.kvs.contains_key(ptsto.k),
                self.kvs[ptsto.k] == ptsto.v
        {}

        #[verifier(external_body)]
        proof fn update(tracked &mut self, v:V, tracked ptsto:&mut GhostMapPointsTo<K,V>)
            requires old(ptsto).id == old(self).id
            ensures
                self.kvs == old(self).kvs.insert(ptsto.k, v),
                self.kvs.contains_key(ptsto.k),
                ptsto.v == v,
                ptsto.k == old(ptsto).k,
                old(self).id == self.id == ptsto.id,
        {}

        #[verifier(external_body)]
        proof fn new() -> (tracked r:GhostMapAuth<K,V>)
            ensures r.kvs == Map::<K,V>::empty()

        {
            unimplemented!();
        }

        #[verifier(external_body)]
        proof fn insert(tracked &mut self, k:K, v:V) -> (tracked ptsto:GhostMapPointsTo<K,V>)
            requires !old(self).kvs.contains_key(k)
            ensures self.kvs == old(self).kvs.insert(k,v),
                    self.id == old(self).id,
                    ptsto.id == self.id,
                    ptsto.k == k,
                    ptsto.v == v,
        {
            unimplemented!();
        }
    }

    struct KvState {
        putOps: Vec<(u64, u64)>,
        ghostKvs: Tracked<GhostMapAuth<u64, u64>>,
    }

    pub open spec fn lookup(m:Map<u64,u64>, k:u64) -> u64 {
        if m.contains_key(k) {
            m[k]
        }
        else {
            0u64
        }
    }

    spec fn gauge_eq(m1:Map<u64,u64>, m2:Map<u64,u64>) -> bool {
        forall|k:u64| lookup(m1, k) == lookup(m2, k)
    }

    spec fn compute_map(ops:Seq<(u64,u64)>) -> Map<u64,u64> {
        ops.fold_left(Map::empty(),
                      (|m:Map<u64,u64>, op:(u64,u64)| m.insert(op.0, op.1))
        )
    }

    impl KvState {
        spec fn kv_inv(self) -> bool {
            gauge_eq(compute_map(self.putOps@), self.ghostKvs@.kvs)
        }

        fn new() -> (ret:(KvState, Tracked<GhostMapPointsTo<u64,u64>>, Tracked<GhostMapPointsTo<u64,u64>>))
            ensures 
                    (ret.0).kv_inv(),
                    (ret.0.ghostKvs@.id == ret.1@.id),
                    (ret.0.ghostKvs@.id == ret.2@.id),
                    (ret.1@.k == 0),
                    (ret.2@.k == 1),
                    (ret.1@.v == ret.2@.v == 0)
        {
            let tracked mut authKvs = GhostMapAuth::new(); 
            let tracked mut ptstoA = authKvs.insert(0u64,0u64);
            let tracked mut ptstoB = authKvs.insert(1u64,0u64);
            let k = KvState{
                putOps: Vec::new(),
                ghostKvs: Tracked(authKvs),
            };
            assert(k.kv_inv());
            (k, Tracked(ptstoA), Tracked(ptstoB))
        }

        fn put(&mut self, k:u64, v:u64, Tracked(ptsto):Tracked<&mut GhostMapPointsTo<u64,u64>>)
            requires
                old(ptsto).id == old(self).ghostKvs@.id,
                old(ptsto).k == k,
                old(self).kv_inv(),
            ensures ptsto.v == v,
                    ptsto.k == old(ptsto).k,
                    old(self).ghostKvs@.id == self.ghostKvs@.id == ptsto.id,
                    self.kv_inv(),
        {
            let ghost oldMap = self.ghostKvs@.kvs;
            let ghost oldPuts = self.putOps@;
            self.putOps.push((k,v));
            proof {
                // let tracked x = self.ghostKvs.borrow_mut();
                (self.ghostKvs.borrow_mut()).update(v, ptsto);
                assert_seqs_equal!(self.putOps@.drop_last() == oldPuts);

                let m1 = compute_map(self.putOps@);
                let m2 = self.ghostKvs@.kvs;
                assert (lookup(m1, k) == lookup(m2, k));

                assert (forall|somek:u64| somek != k ==>  #[trigger] lookup(m2, somek) == lookup(oldMap, somek));
                assert (forall|somek:u64| somek != k ==>  #[trigger] lookup(m1, somek) == lookup(m2, somek));
                // assert(gauge_eq( 
            }
        }

        fn get(&self, k:u64, ptsto_in:Tracked<&GhostMapPointsTo<u64,u64>>) -> (result:u64)
            requires
                self.kv_inv(),
                ptsto_in@.id == self.ghostKvs@.id,
                ptsto_in@.k == k,
            ensures (ptsto_in@.v == result)
        {
            let mut i = 0;
            let tracked ptsto = ptsto_in.get();
            proof {
                // This ensures that k shows up in the map, which helps show that the
                // "assert" is unreachable.
                (self.ghostKvs.borrow()).agree(ptsto);
            }
            let ghost putSeq : Seq<(u64,u64)> = self.putOps@;
            let ghost n = (putSeq.len() as int);

            proof {
                // FIXME: why doesn't this ("take all == l") get figured out
                // automatically? The body of this lemma is empty, and it
                // doesn't seem like there's anything being triggered by it.
                lemma_seq_skip_nothing(self.putOps@, 0);
            }

            assert(self.putOps.len() as int == n);
            while i < self.putOps.len()
                invariant
                    // FIXME: why do the first three clauses need to be in the
                    // loop invariant? Especially the third, which is a pure
                    // mathematical statement.
                    ptsto.id == self.ghostKvs@.id,
                    ptsto.k == k,
                    putSeq.len() as int == n,
                    i <= n,
                    self.putOps@ == putSeq,
                    lookup(self.ghostKvs@.kvs, k) == lookup(compute_map(self.putOps@.take(n-i)), k),
                    ptsto_in@ == ptsto
            {
                let op = self.putOps[self.putOps.len() - 1 - i];
                if op.0 == k {
                    proof {
                        (self.ghostKvs.borrow()).agree(ptsto);
                        assert_seqs_equal!(self.putOps@.take(n-i).drop_last() == self.putOps@.take(n-i-1));
                        assert (compute_map(self.putOps@.take(n-i)) ==
                                compute_map(self.putOps@.take(n-i-1)).insert(op.0,op.1));
                    }
                    return op.1
                }

                proof {
                    assert_seqs_equal!(self.putOps@.take(n-i).drop_last() == self.putOps@.take(n-i-1));
                }
                i += 1;
            }
            0
        }
    }

    struct KvInv {}

    impl lock::Predicate<KvState> for KvInv {
        closed spec fn pred(a:KvState) -> bool {
            a.kv_inv()
        }
    }

    struct KvServer {
        s: lock::Lock<KvState, KvInv>,
        // id: nat,
    }

    impl KvServer {
        fn new() -> (ret:(KvServer,
                          Tracked<GhostMapPointsTo<u64,u64>>,
                          Tracked<GhostMapPointsTo<u64,u64>>))
            ensures 
                    // (ret.0.ghostKvs@.id == ret.1@.id),
                    // (ret.0.ghostKvs@.id == ret.2@.id),
                    (ret.1@.k == 0), (ret.2@.k == 1),
                    (ret.1@.v == ret.2@.v == 0)
        {
            let r = KvState::new();
            let mut kv = r.0;
            let mut ptstoA = r.1;
            let mut ptstoB = r.2;
            return (KvServer{ s: lock::Lock::<KvState,KvInv>::new(kv) }, ptstoA, ptstoB)
        }


        // FIXME: require something about the ptsto.id matching up the server-side id.
        // Ideally, want the lock predicate to take the const id as input. Look
        // at InvariantPredicate to see how that's done.
        fn get(&self, k:u64, Tracked(ptsto):Tracked<&GhostMapPointsTo<u64,u64>>) -> (result:u64)
            requires
                // ptsto_in@.id == self.ghostKvs@.id,
                ptsto.k == k,
            ensures (ptsto.v == result)
        {
            let mut a = self.s.lock();
            let v = a.get(k, Tracked(ptsto));
            self.s.unlock(a);
            return v;
        }

        // FIXME: require something about the ptsto.id matching up the server-side id
        fn put(&self, k:u64, v:u64, Tracked(ptsto):Tracked<&mut GhostMapPointsTo<u64,u64>>)
            requires
                // old(ptsto).id == old(self).ghostKvs@.id,
                old(ptsto).k == k,
            ensures ptsto.v == v,
                    ptsto.k == old(ptsto).k,
                    // old(self).ghostKvs@.id == self.ghostKvs@.id == ptsto.id,
        {
            let mut a = self.s.lock();
            a.put(k, v, Tracked(ptsto));
            self.s.unlock(a);
        }
    }

    fn main() {
        let r = KvServer::new();
        let kv = Arc::new(r.0);
        let mut ptstoA = r.1;
        let mut ptstoB = r.2;
        let kv1 = kv.clone();

        spawn(move ||
        {
            let mut ptstoA = ptstoA;
            let r = (*kv1).get(0, Tracked(ptstoA.borrow()));
            assert(r == 0);

            (*kv1).put(0, 37, Tracked(ptstoA.borrow_mut()));
            let r = (*kv1).get(0, Tracked(ptstoA.borrow()));
            assert(r == 37);
        });

        let r = (*kv).get(1, Tracked(ptstoB.borrow()));
        assert(r == 0);
    }

} // verus!
