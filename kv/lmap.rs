use vstd::{prelude::*,seq_lib::*};

verus! {
    #[verifier::reject_recursive_types(K)]
    pub struct LMap<K,V> {
        kv_vec: Vec<(K, V)>,
    }

    spec fn lookup<K,V>(m:Map<K,V>, k:K) -> Option<V> {
        if m.contains_key(k) {
            Some(m[k])
        }
        else {
            None
        }
    }

    spec fn compute_map<A,B>(ops:Seq<(A,B)>) -> Map<A,B> {
        ops.fold_left(Map::empty(),
                            (|m:Map<A,B>, op:(A,B)| m.insert(op.0, op.1))
        )
    }

    impl<A,B> View for LMap<A,B> {
        type V = Map<A,B>;
        closed spec fn view(&self) -> Map<A,B> {
            compute_map(self.kv_vec@)
        }
    }

    impl<V> LMap<u64,V> {
        // type K = u64;

        pub fn new() -> (ret:LMap<u64,V>)
            ensures ret@ == Map::<u64,V>::empty()
        {
            LMap{
                kv_vec: Vec::new(),
            }
        }

        pub fn get(&self, k:u64) -> (r:Option<&V>)
            ensures
               match r {
                   Some(v) => self@.contains_key(k) && self@[k] == v,
                   None => !self@.contains_key(k)
               }
        {
            let mut i = 0;

            let ghost kv_seq : Seq<(u64,V)> = self.kv_vec@;
            let ghost kvs = self@;
            let ghost n = (kv_seq.len() as int);

            proof {
                lemma_seq_skip_nothing(kv_seq, 0);
            }

            while i < self.kv_vec.len()
                invariant
                    kv_seq.len() as int == n,
                    i <= n,
                    self.kv_vec@ == kv_seq,
                    lookup(kvs, k) == lookup(compute_map(self.kv_vec@.take(n-i)), k),
                    self@ == kvs,
            {
                let op = &self.kv_vec[self.kv_vec.len() - 1 - i];
                if op.0 == k {
                    proof {
                        assert_seqs_equal!(kv_seq.take(n-i).drop_last() == kv_seq.take(n-i-1));
                        assert (compute_map(kv_seq.take(n-i)) ==
                                compute_map(kv_seq.take(n-i-1)).insert(op.0,op.1));
                    }
                    return Some(&op.1)
                }

                proof {
                    assert_seqs_equal!(kv_seq.take(n-i).drop_last() == kv_seq.take(n-i-1));
                }
                i += 1;
            }
            None
        }

        pub fn insert(&mut self, k:u64, v:V)
            ensures self@ == old(self)@.insert(k,v)
        {
            let ghost old_kv_seq = self.kv_vec@;
            self.kv_vec.push((k,v));
            proof {
                assert_seqs_equal!(self.kv_vec@.drop_last() == old_kv_seq);
            }

        }
    }

    fn main() {
    }
}
