// Linked list

use std::mem;
pub struct Node<V> {
    val:V,
    next:Option<Box<Node<V>>>,
}

pub struct List<V> {
    head: Option<Box<Node<V>>>
}

impl<V> List<V> {
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

    pub fn push_back(&mut self, elem:V) {
        match self.head {
            None => {
                self.head = Some(Box::new(Node{val: elem, next: None}));
            }
            Some(_) => {
                // let node : &mut Box<Node<V>> = x;
                // loop {
                // }
            }
        }
    }

    pub fn push_back_recursive(head:&mut Option<Box<Node<V>>>, elem:V) {
        match *head {
            None => {
                *head = Some(Box::new(Node{val: elem, next: None}));
            }
            Some(ref mut x) => {
                Self::push_back_recursive(&mut x.next, elem)
            }
        }
    }

    pub fn push_back_recursive2(head:&mut Option<Box<Node<V>>>, elem:V) {
        match head {
            None => {
                *head = Some(Box::new(Node{val: elem, next: None}));
            }
            Some(x) => {
                Self::push_back_recursive(&mut x.next, elem)
            }
        }
    }
}

pub fn main() {}
