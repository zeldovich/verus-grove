use vstd::{prelude::*,thread::*};
use std::sync::Arc;
mod lock;
mod kv;
use kv::*;

verus! {
    struct KvServer {
        s: lock::Lock<KvState>,
        id: Ghost<nat>,
    }

    spec fn pred_gen(gname:nat) -> spec_fn(KvState) -> bool {
        |s:KvState| s.gname() == gname && s.kv_inv()
    }

    impl KvServer {
        spec fn inv(self) -> bool {
            self.s.get_pred() == pred_gen(self.id@)
        }

        fn new() -> (ret:(KvServer,
                          Tracked<GhostMapPointsTo<u64,u64>>,
                          Tracked<GhostMapPointsTo<u64,u64>>))
            ensures 
                    (ret.1@.k == 0u64),
                    (ret.1@.v == 0u64),
                    (ret.1@.gname() == ret.0.id@),
                    (ret.2@.k == 1u64),
                    (ret.2@.v == 0u64),
                    (ret.2@.gname() == ret.0.id@),
                    ret.0.inv(),
        {
            let r = KvState::new();
            let mut kv = r.0;
            let mut ptstoA = r.1;
            let mut ptstoB = r.2;
            return (KvServer{ id: Ghost(kv.gname()),
                              s: lock::Lock::<KvState>::new(kv, Ghost(pred_gen(kv.gname()))) },
                    ptstoA, ptstoB)
        }

        fn get(&self, k:u64, Tracked(ptsto):Tracked<&GhostMapPointsTo<u64,u64>>) -> (result:u64)
            requires
                self.inv(),
                ptsto.gname() == self.id@,
                ptsto.k == k,
                
            ensures (ptsto.v == result)
        {
            let mut a = self.s.lock();
            let v = a.get(k, Tracked(ptsto));
            self.s.unlock(a);
            return v;
        }

        fn put(&self, k:u64, v:u64, Tracked(ptsto):Tracked<&mut GhostMapPointsTo<u64,u64>>)
            requires
                self.inv(),
                old(ptsto).gname() == self.id@,
                old(ptsto).k == k,

            ensures
                    (ptsto.gname() == self.id@),
                    (ptsto.k == k),
                    (ptsto.v == v),
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

        spawn(move || {
            let mut ptstoA = ptstoA;
            let r = (*kv1).get(0, Tracked(ptstoA.borrow()));
            assert(r == 0);

            (*kv1).put(0, 37, Tracked(ptstoA.borrow_mut()));
            let r = (*kv1).get(0, Tracked(ptstoA.borrow()));
            assert(r == 37);
        });

        spawn(move || {
            let r = (*kv).get(1, Tracked(ptstoB.borrow()));
            assert(r == 0);
        });
    }

} // verus!
