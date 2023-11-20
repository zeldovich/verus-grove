use vstd::{prelude::*,invariant::*,thread::*};
mod lock;
mod kv;
use kv::*;

verus! {

    // possible `state`s
    const UNUSED: u64 = 0;
    const ACTIVE: u64 = 1;
    const DONE: u64 = 2;

    struct WriteRequest {
        val:u64,
        state:u64, // see above for possible values
    }

    // sort-of a "flat combining" register, but with no lock-free accesses and a
    // publication list of length 1.
    pub struct Register {
        plist: lock::Lock<WriteRequest>,
        val: lock::Lock<u64>,
    }

    spec fn gen_val_pred() -> FnSpec(u64) -> bool {
        |val:u64| {
            true
        }
    }

    spec fn gen_plist_pred() -> FnSpec(WriteRequest) -> bool {
        |req:WriteRequest| {
            true
        }
    }

    impl Register {
        spec fn inv(self) -> bool {
            self.val.get_pred() == gen_val_pred() &&
            self.plist.get_pred() == gen_plist_pred()
        }

        fn combiner(&self)
            requires self.inv()
        {
            // repeatedly
            loop
                invariant self.inv()
            {
                let req = self.plist.lock();
                if req.state == ACTIVE {
                    let _ = self.val.lock();
                    self.val.unlock(req.val);
                }
                self.plist.unlock(req);
            }
        }

        fn read(&self) -> u64
            requires self.inv()
        {
            let v = self.val.lock();
            self.val.unlock(v);
            return v;
        }

        fn write(&self, v:u64)
            requires self.inv()
        {
            let mut req;
            // wait for publication list to have a unused slot
            loop {
                req = self.plist.lock();
                if req.state == UNUSED {
                    break
                }
                self.plist.unlock(req);
            }

            // send request
            req.state = ACTIVE;
            req.val = v;
            self.plist.unlock(req);

            // wait for response (of type unit)
            loop {
                req = self.plist.lock();
                if req.state == DONE {
                    break
                }
                self.plist.unlock(req);
            }

            req.state = UNUSED;
            self.plist.unlock(req);
        }
    }

    fn main() {
    }
} // verus!
