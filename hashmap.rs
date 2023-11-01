use crate::prelude::*;
use builtin::*;

use std::collections::HashMap;
use std::hash::*;
use std::borrow::*;
use std::ops::*;

verus!{

    #[verifier(external_type_specification)]
    #[verifier(external_body)]
    #[verifier::accept_recursive_types(K)]
    #[verifier::reject_recursive_types(V)]
    #[verifier::reject_recursive_types(S)]
    pub struct ExHashMap<K, V, S>(HashMap<K, V, S>);

    ////// Declare 'view' function
    pub trait HashMapAdditionalSpecFns<K,V> {
        spec fn spec_index(&self, k: K) -> V;
    }

    impl<A, B, S> View for HashMap<A, B, S> {
        type V = Map<A,B>;
        spec fn view(&self) -> Map<A,B>;
    }

    impl<K, V, S> HashMapAdditionalSpecFns<K,V> for HashMap<K,V,S> {
        #[verifier(inline)]
        open spec fn spec_index(&self, k: K) -> V {
            self.view().index(k)
        }
    }

    impl<K, Q: ?Sized, V, S> Index<&Q> for HashMap<K, V, S>
    where
        K: Eq + Hash + Borrow<Q>,
        Q: Eq + Hash,
        S: BuildHasher,
    {
        type Output = V;
        fn index(&self, key: &Q) -> &V {
            self.get(key).expect("no entry found for key")
        }
    }

    // TODO: this doesn't seem easily supported, see the comment about
    // SliceIndex trait in std_specs/vec.rs
    #[verifier::external_fn_specification]
    #[verifier::when_used_as_spec(spec_vec_len)]
    pub fn ex_map_get<'a, 'b, Q: ?Sized + std::hash::Hash + Eq,
                           K:Eq + std::hash::Hash + std::borrow::Borrow<Q>,
                           V:Eq + std::hash::Hash + Sized,
                           S: std::hash::BuildHasher>
        (m: &'a HashMap<K,V,S>, k:&'b Q) -> (r:Option<&'a V>)
        // where
    // K: Eq + Hash + Borrow<Q>,
    // Q: Eq + Hash + ?Sized,
    // S: BuildHasher,

    {
        m.get(k)
    }
}
