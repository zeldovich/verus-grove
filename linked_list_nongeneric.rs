// Linked list

type V = u64;
use std::mem;
pub struct Node {
    val:V,
    next:Option<Box<Node>>,
}

pub struct List {
    head: Option<Box<Node>>
}

impl List {
    pub fn push_front(&mut self, elem:V) {
        self.head = Some(Box::new(Node{
            val: elem,
            next: mem::take(&mut self.head)
        }));
    }

    pub fn pop_front(&mut self) -> Option<V> {
        // XXX: another limitation of safe Rust: need to ALWAYS maintain
        // exception-safety, even if there's no possible way for there to be an
        // exception. E.g. if we wrote a custom fn that provably wouldn't panic,
        // we should be able to call it while an object is "exception-unsafe".
        let oldhead = mem::replace(&mut self.head, None)?;
        self.head = oldhead.next;
        Some(oldhead.val)
    }

    pub fn push_back_recursive(head:&mut Option<Box<Node>>, elem:V) {
        match *head {
            None => {
                *head = Some(Box::new(Node{val: elem, next: None}));
            }
            Some(ref mut x) => {
                Self::push_back_recursive(&mut x.next, elem)
            }
        }
    }

    pub fn push_back_recursive2(head:&mut Option<Box<Node>>, elem:V) {
        match head {
            &mut None => {
                *head = Some(Box::new(Node{val: elem, next: None}));
            }
            &mut Some(ref mut x) => {
                Self::push_back_recursive(&mut x.next, elem)
            }
        }
    }

    pub fn push_back<'a>(&'a mut self, elem:V) {
        let mut cur_node : &'a mut Option<Box<Node>> = &mut self.head;
        loop {
            match cur_node {
                &mut None => {
                    *cur_node = Some(Box::new(Node{val: elem, next: None}));
                }
                &mut Some(ref mut x) => {
                    cur_node = &mut x.next;
                }
            } 
        }
    }

    pub fn peek_back<'a>(&'a self) -> Option<V> {
        let mut cur_node : &'a Option<Box<Node>> = &self.head;
        let mut prev_val : Option<V> = None;
        loop {
            match cur_node {
                &None => {
                    break;
                }
                &Some(ref x) => {
                    let y : &'a _ = x;
                    prev_val = Some(y.val);
                    cur_node = &y.next;
                }
            } 
        }
        return prev_val;
    }
}

pub fn main() {}
