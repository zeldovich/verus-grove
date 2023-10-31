use vstd::{prelude::*,thread::*,seq_lib::*};
// use std::sync::Arc;
mod lock;
mod kv;
use kv::*;

verus! {
    struct KvErpcState {
        kv:KvState,
        // seenReqIds:Vec<u64>,
        seenReqIds:KvState, //<u64>,
        replies:KvState, //<u64>,
        nextFreshReqId:u64,
    }

    struct KvErpcServer {
        s: lock::Lock<KvErpcState>,
        id: Ghost<nat>,
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

    impl KvErpcServer {
        pub fn get(&self, reqId:u64, k:u64) -> u64 {
            let mut s = self.s.lock();
            // if contains(s.seenReqIds, reqId) {
            //     return
            // }
            // s.kv
            if s.seenReqIds.get(reqId) != 0 {
                return s.replies.get(reqId)
            }
            s.seenReqIds.put(reqId, 1);
            return s.kv.get(k);
        }
        
        pub fn put(&self, reqId:u64, k:u64, v:u64) {
            let mut s = self.s.lock();
            // if contains(s.seenReqIds, reqId) {
            //     return
            // }
            // s.kv
            if s.seenReqIds.get(reqId) != 0 {
                return;
            }
            s.seenReqIds.put(reqId, 1);
            s.kv.put(k, v);
            return;
        }
    }

    fn main() {
    }
} // verus!
