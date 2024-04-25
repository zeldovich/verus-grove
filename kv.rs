use vstd::{prelude::*};
pub mod lmap;

verus! {
    #[verifier::reject_recursive_types(K)]
    pub struct GhostMapAuth<K,V> {
        pub kvs:Map<K,V>,
        pub _id:nat,
    }

    // FIXME: maybe should just expose the gname from here directly? If we get
    // rid of it, there might be a soundness issue where two points-tos might
    // have the same spec gname() when they shouldn't.
    pub struct GhostMapPointsTo<K,V> {
        pub k:K,
        pub v:V,
        pub _id:nat,
    }

    impl<K,V> GhostMapPointsTo<K,V> {
        pub spec fn gname(&self) -> nat;
    }

    impl<K,V> GhostMapAuth<K,V> {
        pub spec fn gname(&self) -> nat;

        #[verifier(external_body)]
        pub proof fn agree(tracked &self, tracked ptsto:&GhostMapPointsTo<K,V>)
            requires ptsto.gname() == self.gname()
            ensures
                self.kvs.contains_key(ptsto.k),
                self.kvs[ptsto.k] == ptsto.v
        {}

        #[verifier(external_body)]
        pub proof fn update(tracked &mut self, v:V, tracked ptsto:&mut GhostMapPointsTo<K,V>)
            requires old(ptsto).gname() == old(self).gname()
            ensures
                self.kvs == old(self).kvs.insert(ptsto.k, v),
                self.kvs.contains_key(ptsto.k),
                ptsto.v == v,
                ptsto.k == old(ptsto).k,
                old(self).gname() == self.gname() == ptsto.gname(),
        {}

        #[verifier(external_body)]
        pub proof fn new() -> (tracked r:GhostMapAuth<K,V>)
            ensures r.kvs == Map::<K,V>::empty()

        {
            unimplemented!();
        }

        #[verifier(external_body)]
        pub proof fn insert(tracked &mut self, k:K, v:V) -> (tracked ptsto:GhostMapPointsTo<K,V>)
            requires !old(self).kvs.contains_key(k)
            ensures self.kvs == old(self).kvs.insert(k,v),
                    self.gname() == old(self).gname(),
                    ptsto.gname() == self.gname(),
                    ptsto.k == k,
                    ptsto.v == v,
        {
            unimplemented!();
        }
    }


    pub struct KvState {
        m: lmap::LMap<u64, u64>,
        ghost_kvs: Tracked<GhostMapAuth<u64, u64>>,
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
        pub closed spec fn gname(self) -> nat {
            self.ghost_kvs@.gname()
        }

        pub closed spec fn kv_inv(self) -> bool {
            gauge_eq(self.m@, self.ghost_kvs@.kvs)
        }

        pub fn new() -> (ret:(KvState, Tracked<GhostMapPointsTo<u64,u64>>, Tracked<GhostMapPointsTo<u64,u64>>))
            ensures 
                    (ret.0).kv_inv(),
                    (ret.0.gname() == ret.1@.gname() == ret.2@.gname()),
                    (ret.1@.k == 0),
                    (ret.2@.k == 1),
                    (ret.1@.v == ret.2@.v == 0)
        {
            let tracked mut authKvs = GhostMapAuth::new(); 
            let tracked mut ptsto_a = authKvs.insert(0u64,0u64);
            let tracked mut ptsto_b = authKvs.insert(1u64,0u64);
            let k = KvState{
                m: lmap::LMap::new(),
                ghost_kvs: Tracked(authKvs),
            };
            assert(k.kv_inv());
            (k, Tracked(ptsto_a), Tracked(ptsto_b))
        }

        pub fn put(&mut self, k:u64, v:u64, Tracked(ptsto):Tracked<&mut GhostMapPointsTo<u64,u64>>)
            requires
                old(ptsto).gname() == old(self).gname(),
                old(ptsto).k == k,
                old(self).kv_inv(),
            ensures ptsto.v == v,
                    ptsto.k == old(ptsto).k,
                    old(self).gname() == self.gname() == ptsto.gname(),
                    self.kv_inv(),
        {
            self.m.insert(k,v);
            proof {
                (self.ghost_kvs.borrow_mut()).update(v,ptsto);
                assert (forall|somek:u64| somek != k ==>  #[trigger] lookup(self.ghost_kvs@.kvs, somek) == lookup(old(self).ghost_kvs@.kvs, somek));
            }
        }

        pub fn get(&self, k:u64, Tracked(ptsto):Tracked<&GhostMapPointsTo<u64,u64>>) -> (result:u64)
            requires
                self.kv_inv(),
                ptsto.gname() == self.gname(),
                ptsto.k == k,
            ensures (ptsto.v == result)
        {
            proof {
                (self.ghost_kvs.borrow()).agree(ptsto);
                assert(lookup(self.m@, k) == lookup(self.ghost_kvs@.kvs, k)); // To trigger gauge_eq
            }
            match self.m.get(k) {
                Some(v) => {
                    *v
                }
                None => {
                    0u64
                }
            }
        }
    }

    fn main() {
        let r = KvState::new();
        let mut kv = r.0;
        let mut ptsto_a = r.1;
        let mut ptsto_b = r.2;

        let r = kv.get(0, Tracked(ptsto_a.borrow()));
        assert(r == 0);

        kv.put(0, 37, Tracked(ptsto_a.borrow_mut()));
        let r = kv.get(1, Tracked(ptsto_b.borrow()));
        assert(r == 0);
        let r = kv.get(0, Tracked(ptsto_a.borrow()));
        assert(r == 37);
    }
} // verus!
