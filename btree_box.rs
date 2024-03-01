// in-memory B+ tree
type KeyType = u64;
type ValueType = usize;
const MAX_DEGREE : usize = 8;

enum Sum<L,R> {
    Left(L),
    Right(R)
}

struct LeafNode {
    keys: [KeyType; MAX_DEGREE-1],
    values: [ValueType; MAX_DEGREE-1],
    length: u8, // length of keys array
}

pub struct InternalNode {
    keys: [KeyType; MAX_DEGREE-1],
    ptrs: [Option<NodePtr>; MAX_DEGREE],
    length: u8, // length of keys array
}

// XXX: this sum type/tagged union requires (at least) an extra bit of
// storage. We could use PPtr and PointsTos as well as a tracked sum of the
// points-tos to avoid this runtime overhead.
type NodePtr = Sum<Box<InternalNode>, Box<LeafNode>>;

pub struct Tree {
    root: Option<NodePtr>
}

impl NodePtr {
    fn split_if_full(&mut self) -> Option<(Self, KeyType)> {
        match self {
            &mut Sum::Left(ref mut internal_node) => {
                if (internal_node.length as usize) < MAX_DEGREE-1 {
                    return None;
                }
                // split
                internal_node.length = internal_node.length/2;
                let split_key = internal_node.keys[internal_node.length as usize];

                let n = internal_node.length as usize;
                let mut sibling = Box::new(InternalNode{
                    keys: [0; MAX_DEGREE-1],
                    ptrs: std::array::from_fn(|_| None),
                    length: (MAX_DEGREE - n - 1) as u8,
                });
                for i in n+1 .. MAX_DEGREE {
                    sibling.ptrs[i - n] = internal_node.ptrs[i].take();
                }
                for i in n+1 .. MAX_DEGREE-1 {
                    sibling.keys[i - n] = internal_node.keys[i];
                }
                return Some((Sum::Left(sibling), split_key));
            }
            &mut Sum::Right(ref mut leaf_node) => {
                if (leaf_node.length as usize) < MAX_DEGREE-1 {
                    return None;
                }
                // split
                leaf_node.length = leaf_node.length/2;
                let split_key = leaf_node.keys[leaf_node.length as usize - 1];
                let n = leaf_node.length as usize;
                let mut sibling = Box::new(LeafNode{
                    keys: [0; MAX_DEGREE-1],
                    values: [0; MAX_DEGREE-1],
                    length: (MAX_DEGREE - 1 - n) as u8,
                });
                for i in n .. MAX_DEGREE-1 {
                    sibling.keys[i - n] = leaf_node.keys[i];
                    sibling.values[i - n] = leaf_node.values[i];
                }
                return Some((Sum::Right(sibling), split_key));
            }
        }
    }
}

impl Tree {
    pub fn new() -> Self {
        Tree{root: None}
    }

    pub fn get(&self, key:KeyType) -> Option<ValueType> {
        let mut cur_node : &NodePtr = self.root.as_ref()?;

        loop {
            match cur_node {
                &Sum::Left(ref internal_node) => {
                    // find the next node
                    let mut index = internal_node.length as usize;
                    for (i,k) in internal_node.keys.iter().take(internal_node.length as usize).enumerate() {
                        if key <= *k {
                            index = i;
                            break;
                        }
                    }
                    cur_node = internal_node.ptrs[index].as_ref().unwrap();
                }
                &Sum::Right(ref leaf_node) => {
                    for (i,k) in leaf_node.keys.iter().take(leaf_node.length as usize).enumerate() {
                        if *k == key {
                            return Some(leaf_node.values[i]);
                        }
                    }
                    return None;
                }
            }
        }
    }

    pub fn put(&mut self, key:KeyType, value:ValueType) {
        // maybe split root
        // XXX: This is confusing because of exception safety. E.g. it uses
        // self.root.take(), because the nicer alternative of matching on
        // (&mut self.root) and getting a `ref mut` to the root_node field
        // results in challenges with updating the root node to a new node while
        // still owning the old root node so the new node can point to it.
        let mut cur_node : &mut NodePtr =
            match self.root.take() {
                None => {
                    let mut new_root = Box::new(LeafNode{
                        keys:   [0; MAX_DEGREE-1],
                        values: [0; MAX_DEGREE-1],
                        length: 1,
                    });
                    new_root.keys[0] = key;
                    new_root.values[0] = value;
                    self.root = Some(Sum::Right(new_root));
                    return;
                },
                Some(mut root_node) => {
                    if let Some((new_sibling, split_key)) = root_node.split_if_full() {
                        let mut new_root = Box::new(
                            InternalNode{
                                keys:   [0; MAX_DEGREE-1],
                                ptrs: std::array::from_fn(|_| None),
                                length: 1,
                            });
                        new_root.keys[0] = split_key;
                        new_root.ptrs[0] = Some(root_node);
                        new_root.ptrs[1] = Some(new_sibling);
                        self.root = Some(Sum::Left(new_root));
                    } else {
                        self.root = Some(root_node);
                    }
                    self.root.as_mut().unwrap()
                },
            };

        loop {
            match cur_node {
                &mut Sum::Right(ref mut leaf_node) => {
                    let mut i = 0;
                    let n = leaf_node.length as usize;
                    // XXX: iterates backwards because elements are shifted to the
                    // right, so we start from the right.
                    while i < n && leaf_node.keys[(n-1) - i] > key {
                        leaf_node.keys[(n-1) - i + 1] = leaf_node.keys[(n-1) - i];
                        leaf_node.values[(n-1) - i + 1] = leaf_node.values[(n-1) - i];
                        i += 1;
                    }
                    leaf_node.length += 1;
                    leaf_node.keys[(n-1) - i + 1] = key;
                    leaf_node.values[(n-1) - i + 1] = value;
                    return;
                }
                &mut Sum::Left(ref mut internal_node) => {
                    // find next child
                    let mut index = internal_node.length as usize;
                    for (i,k) in internal_node.keys.iter().take(internal_node.length as usize).enumerate() {
                        if key <= *k {
                            index = i;
                            break;
                        }
                    }
                    let next_node_ptr = internal_node.ptrs[index].as_mut().unwrap();
                    if let Some((new_sibling, split_key)) = next_node_ptr.split_if_full() {
                        // move all the pointers ahead of `index` to the right:
                        for i in ((index + 1).. (internal_node.length as usize + 1)).rev() {
                            internal_node.ptrs[i + 1] = internal_node.ptrs[i].take();
                        }
                        internal_node.ptrs[index + 1] = Some(new_sibling);
                        for i in ((index).. (internal_node.length as usize)).rev() {
                            internal_node.keys[i + 1] = internal_node.keys[i];
                        }
                        internal_node.keys[index] = split_key;
                        internal_node.length += 1;
                    }
                    cur_node = internal_node.ptrs[index].as_mut().unwrap();
                    // cur_node = next_node_ptr;
                }
            }
        }
    }
}

pub fn main() {
    let mut t = Tree::new();
    for i in 0..1000 {
        t.put(37 * i, 100 * i as usize);
    }
    println!("851 = {}", t.get(851).unwrap());
}
