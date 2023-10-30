use vstd::{prelude::*,seq_lib::*};

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
        proof fn agree(&self, ptsto:Tracked<&GhostMapPointsTo<K,V>>)
            requires ptsto@.id == self.id
            ensures
                self.kvs.contains_key(ptsto@.k),
                self.kvs[ptsto@.k] == ptsto@.v
        {}
        
        #[verifier(external_body)]
        fn update(&mut self, v:V, Tracked(ptsto):Tracked<&mut GhostMapPointsTo<K,V>>)
            requires ptsto.id == old(self).id
            ensures
                self.kvs.contains_key(ptsto.k),
                ptsto.v == v,
                old(self).id == self.id == ptsto.id,
        {}

        // #[verifier(external_body)]
        // proof fn new() -> (r:GhostMapAuth<K,V>)
            // ensures 
                // r.kvs.len() == 0
        // {
        // }
    }

    // Single node in the list
    struct KvServer {
        putOps: Vec<(u64, u64)>,
        ghostKvs: Tracked<GhostMapAuth<u64, u64>>,
        id: nat,
    }

    spec fn computeMap(ops:Seq<(u64,u64)>) -> Map<u64,u64> {
        ops.fold_left(Map::empty(),
                      (|m:Map<u64,u64>, op:(u64,u64)| m.insert(op.0, op.1))
        )
    }

    // pub open spec fn equal_for_key(m1:Map<u64,u64>, m2:Map<u64,u64>, k:u64) -> bool {
        // (m1.contains_key(k) <==> m2.contains_key(k)) &&
        // m1[k] == m2[k]
    // }

    // pub proof fn equal_for_key_trans(m1:Map<u64,u64>, m2:Map<u64,u64>, m3:Map<u64,u64>, k:u64)
        // requires equal_for_key(m1,m2,k),
                 // equal_for_key(m2,m3,k)
        // ensures equal_for_key(m1,m3,k)
    // {
    // }

    impl KvServer {
        spec fn inv(self) -> bool {
            computeMap(self.putOps@) == self.ghostKvs@.kvs
        }

        fn put(&mut self, k:u64, v:u64, ptsto:&mut GhostMapPointsTo<u64,u64>)
            requires
                old(ptsto).id == old(self).ghostKvs@.id,
                old(ptsto).k == k,
                old(self).inv(),
            ensures ptsto.v == v,
                    old(self).ghostKvs@.id == self.ghostKvs@.id == ptsto.id,
                    self.inv(),
        {
            self.putOps.push((k,v));
            proof {
                let mut x = self.ghostKvs@;
                let tracked x = x.tracked_remove
                x.update(v, Tracked(&mut ptsto));
            }
        }

        fn get(&self, k:u64, ptsto:&GhostMapPointsTo<u64,u64>) -> (result:u64)
            requires
                self.inv(),
                ptsto.id == self.ghostKvs@.id,
                ptsto.k == k,
            ensures (ptsto.v == result)
        {
            let mut i = 0;
            proof {
                // This ensures that k shows up in the map, which helps show that the
                // "assert" is unreachable.
                self.ghostKvs@.agree(Tracked(ptsto));
            }
            // let ghost putOps = self.putOps;
            let ghost putSeq : Seq<(u64,u64)> = self.putOps@;
            let ghost n = (putSeq.len() as int);

            proof {
                // FIXME: why doesn't this ("take all == l") get figured out
                // automatically? The body of this lemma is empty, and it
                // doesn't seem like there's anything being triggered by it.
                lemma_seq_skip_nothing(self.putOps@, 0);
                // lemma_seq_properties::<(u64,u64)>();
                // assert(self.opsSeq.subrange(0,self.opsSeq.len() as int) == self.opsSeq);
                // assert(self.opsSeq.take(n) == self.opsSeq);
                // assert(self.opsSeq.take(n-i) == self.opsSeq);
                // assert(self.ghostKvs@.kvs == computeMap(self.opsSeq.take(n-i)));
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
                    self.ghostKvs@.kvs.is_equal_on_key(computeMap(self.putOps@.take(n-i)),
                                k),
            {
                let op = self.putOps[self.putOps.len() - 1 - i];
                if op.0 == k {
                    proof {
                        assert_seqs_equal!(self.putOps@.take(n-i).drop_last() == self.putOps@.take(n-i-1));
                        assert (computeMap(self.putOps@.take(n-i)) ==
                                computeMap(self.putOps@.take(n-i-1)).insert(op.0,op.1));
                        self.ghostKvs@.agree(Tracked(ptsto));
                        assert(self.ghostKvs@.kvs[op.0] == op.1);
                        assert(self.ghostKvs@.kvs[op.0] == op.1);
                        assert(ptsto.v == op.1);
                    }
                    return op.1
                }

                // proof {
                    // assert(putSeq.len() as int == n);
                    // assert(self.putOps.len() == self.putOps@.len());
                    // assert(self.putOps@.len() as int == n);
                    // assert(self.putOps.len() as int == n);
                    // assert(i < self.putOps.len());
                    // assert(i < n);
                // }
                proof {
                    // lemma_seq_properties::<(u64,u64)>();
                    //assert (self.putOps@.take(n-i) == self.putOps@.take(n-i-1) + seq![(op.0,op.1)]);
                    // assert(self.putOps@.take(n-i).last() == op);
                    assert_seqs_equal!(self.putOps@.take(n-i).drop_last() == self.putOps@.take(n-i-1));

                    // assert (computeMap(self.putOps@.take(n-i)) ==
                            // computeMap(self.putOps@.take(n-i-1)).insert(op.0,op.1));
                    // assert (op.0 != k);
                    // let ghost m1 = computeMap(self.putOps@.take(n-i-1));
                    // let ghost m2 = computeMap(self.putOps@.take(n-i-1)).insert(op.0,op.1);
                    // if m1.contains_key(k) {
                        // assert(m2.contains_key(k));
                        // assert(m2[k] == m1[k]);
                    // }
                    // if m2.contains_key(k) {
                        // assert(m1.contains_key(k));
                        // assert(m2[k] == m1[k]);
                    // }
                    // assert (equal_for_key(m1,m2,k));
                }
                i += 1;
            }
            assert(false);
            0
            // panic!("unreachable");
        }
    }

    fn main() {
    }

} // verus!
