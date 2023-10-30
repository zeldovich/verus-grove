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
        tracked ghostKvs: GhostMapAuth<u64, u64>,
        id: nat,
    }

    spec fn computeMap(ops:Seq<(u64,u64)>) -> Map<u64,u64> {
        ops.fold_left(Map::empty(),
                      (|m:Map<u64,u64>, op:(u64,u64)| m.insert(op.0, op.1))
        )
    }


    fn example(Tracked(x): Tracked<&mut u64>)
    {
    }

    fn test() {
        let tracked mut u64 = 0u64;

        example(Tracked(&mut u64));
    }

    impl KvServer {
        spec fn inv(self) -> bool {
            computeMap(self.putOps@) == self.ghostKvs.kvs
        }

        fn put(&mut self, k:u64, v:u64, Tracked(ptsto):Tracked<&mut GhostMapPointsTo<u64,u64>>)
            requires
                old(ptsto).id == old(self).ghostKvs.id,
                old(ptsto).k == k,
                old(self).inv(),
            ensures ptsto.v == v,
                    ptsto.k == old(ptsto).k,
                    old(self).ghostKvs.id == self.ghostKvs.id == ptsto.id,
                    self.inv(),
        {
            let ghost oldMap = self.ghostKvs.kvs;
            let ghost oldPuts = self.putOps@;
            self.putOps.push((k,v));
            proof {
                self.ghostKvs.update(v, ptsto);
                assert_seqs_equal!(self.putOps@.drop_last() == oldPuts);
            }
        }

        fn get(&self, k:u64, tracked ptsto:&GhostMapPointsTo<u64,u64>) -> (result:u64)
            requires
                self.inv(),
                ptsto.id == self.ghostKvs.id,
                ptsto.k == k,
            ensures (ptsto.v == result)
        {
            let mut i = 0;
            proof {
                // This ensures that k shows up in the map, which helps show that the
                // "assert" is unreachable.
                self.ghostKvs.agree(ptsto);
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
                    ptsto.id == self.ghostKvs.id,
                    ptsto.k == k,
                    putSeq.len() as int == n,
                    i <= n,
                    self.putOps@ == putSeq,
                    self.ghostKvs.kvs.is_equal_on_key(computeMap(self.putOps@.take(n-i)),
                                k),
            {
                let op = self.putOps[self.putOps.len() - 1 - i];
                if op.0 == k {
                    proof {
                        self.ghostKvs.agree(ptsto);
                        assert_seqs_equal!(self.putOps@.take(n-i).drop_last() == self.putOps@.take(n-i-1));
                        assert (computeMap(self.putOps@.take(n-i)) ==
                                computeMap(self.putOps@.take(n-i-1)).insert(op.0,op.1));
                    }
                    return op.1
                }

                proof {
                    assert_seqs_equal!(self.putOps@.take(n-i).drop_last() == self.putOps@.take(n-i-1));
                }
                i += 1;
            }
            assert(false);
            0
        }
    }

    fn main() {
    }

} // verus!
