use vstd::{prelude::*,thread::*};
use std::sync::Arc;
mod lock;
mod kv;
use kv::*;

verus! {
    spec fn predGen(id:nat) -> FnSpec(KvState) -> bool {
        |s:KvState| s.ghostKvs@.id == id && s.kv_inv()
    }

    struct KvServer {
        s: lock::Lock<KvState>,
        id: Ghost<nat>,
    }

    impl KvServer {
        spec fn inv(self) -> bool {
            self.s.getPred() == predGen(self.id@)
        }

        fn new() -> (ret:(KvServer,
                          Tracked<GhostMapPointsTo<u64,u64>>,
                          Tracked<GhostMapPointsTo<u64,u64>>))
            ensures 
                    (ret.0.id@ == ret.1@.id == ret.2@.id),
                    (ret.1@.k == 0), (ret.2@.k == 1),
                    (ret.1@.v == ret.2@.v == 0),
                    ret.0.inv(),
        {
            let r = KvState::new();
            let mut kv = r.0;
            let mut ptstoA = r.1;
            let mut ptstoB = r.2;
            let ghost id = kv.ghostKvs@.id;
            return (KvServer{ id: Ghost(id),
                              s: lock::Lock::<KvState>::new(kv, Ghost(predGen(id))) },
                    ptstoA, ptstoB)
        }


        // FIXME: require something about the ptsto.id matching up the server-side id.
        // Ideally, want the lock predicate to take the const id as input. Look
        // at InvariantPredicate to see how that's done.
        fn get(&self, k:u64, Tracked(ptsto):Tracked<&GhostMapPointsTo<u64,u64>>) -> (result:u64)
            requires
                self.inv(),
                ptsto.id == self.id@,
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
                self.inv(),
                old(ptsto).id == self.id@,
                old(ptsto).k == k,
            ensures ptsto.v == v,
                    ptsto.k == old(ptsto).k,
                    self.id@ == ptsto.id,
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
