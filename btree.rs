// in-memory B+ tree
use vstd::{prelude::*, ptr::*};

verus! {
type KeyType = u64;
type ValueType = usize;
const MAX_DEGREE : usize = 8;

pub struct BpTreeNode {
    keys: [KeyType; MAX_DEGREE-1],
    ptrs: [usize; MAX_DEGREE],
    ptstos: Tracked<[PointsTo<BpTreeNode>; MAX_DEGREE]>, // FIXME: option pointsto
    length: u8, // length of keys array
    is_leaf: bool,
}

pub struct BpTree {
    root: PPtr<BpTreeNode>,
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
// XXX: this escrow-based thing is what lifetimes (and e.g. the lifetime logic)
// already handle.
#[verifier(external_body)]
pub fn get(node_ptr:usize, ptsto:Tracked<&PointsTo<BpTreeNode>>, key:KeyType) -> (ov:Option<ValueType>) {
    // FIXME: if we go with a big_sep of points-tos, then when we take one out,
    // we'd be mutating the BpTreeNode's ptstos field, which might mean we have
    // to do some take+put/replace, despite this being read-only.

    let mut node_ptr : PPtr<BpTreeNode> = PPtr::from_usize(node_ptr);
    let mut ptsto = ptsto;
    loop {
        let x = node_ptr.borrow(ptsto);
        if x.is_leaf {
            // scan the leaf
            for (i, k) in x.keys.iter().enumerate() {
                if *k == key {
                    return Some(x.ptrs[i]);
                }
            }
            return None;
        } else {
            // find the next node to search
            let mut next_child_index : usize = x.length as usize;
            for (i,k) in x.keys.iter().enumerate() {
                if key <= *k {
                    next_child_index = i;
                    break;
                }
            }
            node_ptr = PPtr::from_usize(x.ptrs[next_child_index]);
            ptsto = Tracked(&x.ptstos.borrow()[next_child_index as int]);
            // FIXME: what's the lifetime on this reference? This probably will
            // fail the rust typechecker.
        }
    }
}

impl BpTree {
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
        // newRoot = 
        self.root.put(Tracked::assume_new(),
                      BpTreeNode{is_leaf: false,
                                 keys: [split_key; MAX_DEGREE - 1],
                                 ptrs: [old_root_ptr.to_usize(), new_right_sibling, 0, 0, 0, 0, 0, 0],
                                 length: 1,
                                 ptstos: Tracked::assume_new(),
                      });
    }

    let mut node: &mut  = self.root;
    loop {
        if node.borrow(Tracked::assume_new()).is_leaf {
            // insert KV into here
            unimplemented!();
        }
    }
}
}

pub fn main() {}
}
