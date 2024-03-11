// in-memory B+ tree
use vstd::{prelude::*, ptr::*};

verus! {

// FIXME: for loop on a slice iter

enum Sum<L,R> {
    Left(L),
    Right(R)
}

type KeyType = u64;
type ValueType = usize;
const MAX_DEGREE : usize = 8;

pub struct BpTreeNode {
    keys: [KeyType; MAX_DEGREE-1],
    ptrs: [usize; MAX_DEGREE],
    // FIXME: Would a a Tracked<Seq<PointsTo>> work better? A: No, Seq only has spec fns.
    ptstos: [Tracked<Option<Sum<PointsTo<BpTreeNode>, PointsTo<ValueType>>>>; MAX_DEGREE], // FIXME: option pointsto
    length: u8, // length of keys array

    height: Ghost<u64>,
    sigma: Ghost<Map<KeyType, ValueType>>,
}

pub struct BpTree {
    root: PPtr<BpTreeNode>,
    height: u64,
    ptsto: Tracked<PointsTo<BpTreeNode>>,
}

impl BpTreeNode {
    // NOTE: implementing here would be annoying because the top-level node
    // would be a &mut BpTreeNode, whereas all the ones below would be PPtr's. If
    // we did it recursively, might be possible to turn the PPtr into a &mut
    // with a new "borrow_mut" function.
    
    // FIXME: also need to return PointsTo
    #[verifier(external_body)]
    fn split(&mut self) -> (KeyType, usize) {
        unimplemented!();
    }

    closed spec fn inv(self) -> bool
        decreases (self.height@)
    {
        // ptstos and ptrs are in sync
        &&& (0 <= self.length <= MAX_DEGREE-1)
        &&& if self.height == 0 {
            // agrees completely with map
            &&& (forall |i:int| 0 <= i < self.length ==>
                 {
                     &&& (#[trigger] self.ptstos[i])@.is_Some()
                     &&& match self.ptstos[i]@.unwrap() {
                         Sum::Left(_) => {
                             false
                         }
                         Sum::Right(ptsto) => {
                             &&& ptsto@.pptr == self.ptrs[i]
                             &&& ptsto@.value.is_Some()
                             &&& lookup(self.sigma@, self.keys[i]) == ptsto@.value
                         }
                     }
                 }
            )
            &&& self.sigma@.dom() == self.keys@.take(self.length as int).to_set()
        } else {
            // internal node
            &&& (forall |i:int| 0 <= i <= self.length ==>
                 {
                     &&& self.ptstos[i]@.is_Some()
                     &&& match self.ptstos[i]@.unwrap() {
                         Sum::Left(ptsto) => {
                             &&& ptsto@.pptr == self.ptrs[i]
                             &&& ptsto@.value.is_Some()
                             &&& ptsto@.value.unwrap().height@ == self.height@ - 1
                             &&& ptsto@.value.unwrap().inv()
                         }
                         Sum::Right(_) => {
                             false
                         }
                     }
                 }
            )
        }
    }
}

// Challenge: non-recursive pointer-chasing
// One general approach: big escrow.
//  P x := ∃ y, ((x ↦ y) ∗ P y ∨ x ↦ LEAF)
//  (own_escrow ={⊤}=∗ P root) ∗ P2 root,
//   where
//  P2 x := ∃ y, inv ((x ↦ y ∗ P2 y) ∨ own_acc ∨ is_escrow_done)
//
// P root
// 
// Other approach:
//
// XXX: this escrow-based thing is what lifetimes (and e.g. the RustBelt
// lifetime logic) already handle.

pub fn ref_tracked_to_tracked_ref<T>(r:&Tracked<T>) -> (ret:Tracked<&T>)
        ensures r@ == ret@
{
    return Tracked(r.borrow())
}

pub proof fn tracked_as_ref<T>(tracked o:&Option<T>) -> (tracked a: Option<&T>)
    ensures
        a.is_Some() <==> o.is_Some(),
        a.is_Some() ==> o.get_Some_0() == a.get_Some_0(),
{
    match o {
        Option::Some(x) => Option::Some(x),
        Option::None => Option::None,
    }
}

spec fn lookup(m:Map<KeyType, ValueType>, key:KeyType) -> Option<ValueType> {
    if m.contains_key(key) {
        Some(m[key])
    } else {
        None
    }
}

fn get(node_ptr:usize, height:u64, ptsto_in:&Tracked<PointsTo<BpTreeNode>>, key:KeyType) -> (ov:Option<ValueType>)
    requires
        ptsto_in@@.value.is_Some(),
        ptsto_in@@.value.unwrap().inv(),
        ptsto_in@@.value.unwrap().height == height,
        ptsto_in@@.pptr == node_ptr,
        ptsto_in@@.value.is_Some(),
    ensures
        ov == lookup(ptsto_in@@.value.unwrap().sigma@, key)
{
    let mut node_ptr : PPtr<BpTreeNode> = PPtr::from_usize(node_ptr);

    // FIXME: if we introduce a new immutable binding to ptsto_in, the postcond fails.

    let mut ptsto = ref_tracked_to_tracked_ref(ptsto_in);
    let mut height = height;
    loop
        invariant_ensures
          ptsto@@.pptr == node_ptr.id(),
          ptsto@@.value.is_Some(),
          ptsto@@.value.unwrap().inv(),
          ptsto@@.value.unwrap().height == height,
          lookup(ptsto@@.value.unwrap().sigma@, key) == lookup(ptsto_in@@.value.unwrap().sigma@, key)
    {
        let node = node_ptr.borrow(ptsto);
        if height == 0 {
            // scan the leaf
            // for (i, k) in node.keys.iter().enumerate() {
            // for i in 0..(node.length as usize)
            let mut i = 0;
            while i < node.length as usize
                invariant node.inv(),
                0 <= i <= node.length,
                !node.keys@.take(i as int).contains(key),
            {
                if node.keys[i] == key {
                    let y = &node.ptstos[i];
                    let tracked val_ptsto;
                    proof {
                        val_ptsto = match &tracked_as_ref(y.borrow()).tracked_unwrap() {
                            Sum::Left(ptsto) => {
                                assert(false);
                                proof_from_false()
                            }
                            Sum::Right(ptsto) => {
                                ptsto
                            }
                        }
                    }

                    assert(lookup(ptsto@@.value.unwrap().sigma@, key) == val_ptsto@.value);
                    return Some(*PPtr::from_usize(node.ptrs[i]).borrow(Tracked(val_ptsto)));
                }
            }
            assert(lookup(ptsto_in@@.value.unwrap().sigma@, key) == None::<ValueType>);
            return None;
        } else {
            // find the next node to search
            let mut next_child_index : usize = node.length as usize;
            // for (i,k) in node.keys.iter().enumerate() {
            // for i in 0..(node.length as usize)
            let mut i = 0;
            while i < node.length as usize 
                invariant_ensures
                  node.inv(),
                  0 <= next_child_index <= node.length,
            {
                if key <= node.keys[i] {
                    next_child_index = i;
                    break;
                }
            }
            node_ptr = PPtr::from_usize(node.ptrs[next_child_index]);
            let tracked next_ptsto;
            let y = &node.ptstos[next_child_index];
            proof {
                assert(node.height != 0);
                let tracked y : &Option<_> = y.borrow();
                assert(y.is_Some());
                let tracked y = tracked_as_ref(y).tracked_unwrap();

                match &y {
                    Sum::Left(ptsto) => {
                        next_ptsto = ptsto;
                    }
                    Sum::Right(ptsto) => {
                        assert(false);
                        next_ptsto = proof_from_false();
                    }
                }
            }
            ptsto = Tracked(next_ptsto);
            height = height - 1;
        }
    }
}

impl BpTree {
    /*
#[verifier(external_body)]
pub fn put(&mut self, key:KeyType, value:ValueType) {
    if self.root.borrow(Tracked(self.ptsto.borrow())).length as usize == MAX_DEGREE - 1 {
        // XXX: there's no borrow_mut(). Adding that is non-trivial.
        // The caller of pptr.borrow_mut(ptsto) would give up the ptsto for some
        // amount of time, and in exchange get a mutable reference it can use to
        // modify the underlying data. Once the lifetime of the mut ref ends,
        // ptsto becomes live again, but its value may have changed. Would need
        // an effective way of connecting the value of the &mut reference to the
        // value in the points-to.
        // 
        let mut root = self.root.take(Tracked::assume_new());
        let (split_key, new_right_sibling) = root.split();
        // allocate new left node
        let (old_root_ptr, old_root_ptsto, old_root_dealloc) = PPtr::<BpTreeNode>::empty();
        let newRoot = BpTreeNode{is_leaf: false,
                                 keys: [split_key; MAX_DEGREE - 1],
                                 ptrs: [old_root_ptr.to_usize(), new_right_sibling, 0, 0, 0, 0, 0, 0],
                                 length: 1,
                                 ptstos: std::array::from_fn(|_| Tracked::assume_new()),
                      };
        self.root.put(Tracked::assume_new(), newRoot);
    }

    /*
    let mut node: &mut _ = self.root;
    loop {
        if node.borrow(Tracked::assume_new()).is_leaf {
            // insert KV into here
            unimplemented!();
        }
    }
    */
}
*/
}

pub fn main() {}
}
