use vstd::{prelude::*};
pub mod lmap;

verus! {
    pub struct GhostMapAuth<#[verifier::reject_recursive_types] K,V> {
        pub id:nat,
        pub kvs:Map<K,V>,
    }

    pub struct GhostMapPointsTo<K,V> {
        pub id:nat,
        pub k:K,
        pub v:V,
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


    pub struct KvState {
        m: lmap::LMap<u64, u64>,
        ghostKvs: Tracked<GhostMapAuth<u64, u64>>,
    }

    spec fn lookup(m:Map<u64,u64>, k:u64) -> u64 {
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

    impl KvState {
        pub closed spec fn get_id(self) -> nat {
            self.ghostKvs@.id
        }

        pub closed spec fn kv_inv(self) -> bool {
            gauge_eq(self.m@, self.ghostKvs@.kvs)
        }

        pub fn new() -> (ret:(KvState, Tracked<GhostMapPointsTo<u64,u64>>, Tracked<GhostMapPointsTo<u64,u64>>))
            ensures 
                    (ret.0).kv_inv(),
                    (ret.0.get_id() == ret.1@.id == ret.2@.id),
                    (ret.1@.k == 0),
                    (ret.2@.k == 1),
                    (ret.1@.v == ret.2@.v == 0)
        {
            let tracked mut authKvs = GhostMapAuth::new(); 
            let tracked mut ptstoA = authKvs.insert(0u64,0u64);
            let tracked mut ptstoB = authKvs.insert(1u64,0u64);
            let k = KvState{
                m: lmap::LMap::new(),
                ghostKvs: Tracked(authKvs),
            };
            assert(k.kv_inv());
            (k, Tracked(ptstoA), Tracked(ptstoB))
        }

        pub fn put(&mut self, k:u64, v:u64, Tracked(ptsto):Tracked<&mut GhostMapPointsTo<u64,u64>>)
            requires
                old(ptsto).id == old(self).get_id(),
                old(ptsto).k == k,
                old(self).kv_inv(),
            ensures ptsto.v == v,
                    ptsto.k == old(ptsto).k,
                    old(self).get_id() == self.get_id() == ptsto.id,
                    self.kv_inv(),
        {
            self.m.insert(k,v);
            proof {
                (self.ghostKvs.borrow_mut()).update(v,ptsto);
                assert (forall|somek:u64| somek != k ==>  #[trigger] lookup(self.ghostKvs@.kvs, somek) == lookup(old(self).ghostKvs@.kvs, somek));
            }
        }

        pub fn get(&self, k:u64, Tracked(ptsto):Tracked<&GhostMapPointsTo<u64,u64>>) -> (result:u64)
            requires
                self.kv_inv(),
                ptsto.id == self.get_id(),
                ptsto.k == k,
            ensures (ptsto.v == result)
        {
            proof {
                (self.ghostKvs.borrow()).agree(ptsto);
                assert(lookup(self.m@, k) == lookup(self.ghostKvs@.kvs, k)); // To trigger gauge_eq
            }
            match self.m.get(k) {
                Some(v) => {
                    *v
                }
                None => {
                    assume(false);
                    0u64
                }
            }
        }
    }

    fn main() {
        let r = KvState::new();
        let mut kv = r.0;
        let mut ptstoA = r.1;
        let mut ptstoB = r.2;

        let r = kv.get(0, Tracked(ptstoA.borrow()));
        assert(r == 0);

        kv.put(0, 37, Tracked(ptstoA.borrow_mut()));
        let r = kv.get(1, Tracked(ptstoB.borrow()));
        assert(r == 0);
        let r = kv.get(0, Tracked(ptstoA.borrow()));
        assert(r == 37);
    }

} // verus!
