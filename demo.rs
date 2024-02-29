#![feature(mutex_unlock)]
use vstd::{prelude::*};
use std::sync::{Arc,Mutex};
use std::thread;

verus! {
    // core of linearity
    pub struct SomeStuff {}

    fn foo(s:SomeStuff) {}

    fn test_foo(s:SomeStuff) {
        foo(s);
        // foo(s); // fails if uncommented
    }


    



    


    // invariants ~ mutex
    #[verifier::external]
    fn bar(s:Arc<Mutex<SomeStuff>>) {
        let a = s.lock().unwrap();
        // do some stuff with a
        Mutex::unlock(a);
    }

    #[verifier::external]
    fn test_bar(s:SomeStuff) {
        let a = Arc::new(Mutex::new(s));
        let a2 = a.clone();
        thread::spawn (move || {
            bar(a);
        });
        thread::spawn (|| {
            bar(a2);
        });
    }










    
    // Generalized resources
    #[verifier::external_body]
    pub struct GhostName {
    }

    #[verifier::external_body]
    pub struct EpochPointsTo {
    }

    #[verifier::external_body]
    pub struct EpochLowerBound {
    }

    impl EpochPointsTo {
        spec fn value(self) -> nat;
        spec fn id(self) -> nat;
    }

    impl EpochLowerBound {
        spec fn value(self) -> nat;
        spec fn id(self) -> nat;
    }

    #[verifier::external_body]
    proof fn increase_epoch(tracked ptsto_in:EpochPointsTo) -> (tracked ptsto:EpochPointsTo)
        ensures ptsto.value() == ptsto_in.value() + 1,
                ptsto.id() == ptsto_in.id()
    {
        unimplemented!();
    }

    #[verifier::external_body]
    proof fn lower_bound_inequality(tracked ptsto:&EpochPointsTo,
                                    tracked lb:&EpochLowerBound)
        requires lb.id() == ptsto.id()
        ensures lb.value() <= ptsto.value(),
    {
    }

    fn config_service(tracked ptsto_in:EpochPointsTo,
                      tracked lb:EpochLowerBound,
    )
        requires ptsto_in.id() == lb.id(),
                 ptsto_in.value() == 37
    {
        let tracked mut ptsto = ptsto_in;
        // do some stuff ...
        proof {
            ptsto = increase_epoch(ptsto);
        }
        assert(ptsto.value() == 38);
        // do some more stuff ...

        proof {
            lower_bound_inequality(&ptsto, &lb);
            assert(lb.value() <= 38);
        }
    }













    // Higher-order state can lead to inconsistency
    #[verifier::external_body]
    fn landins_knot() {
        let r : Arc<Mutex<Arc<dyn Fn(u64) -> u64>>> =
            Arc::new(Mutex::new(Arc::new(
                |x:u64| {
                    return x;
                }
            )));

        let r2 = r.clone();
        let f : Arc<dyn Fn(u64) -> u64> = Arc::new(
            move |x:u64| -> u64 {
                println!("knot");
                let r_guard = r2.lock().unwrap();
                let r_fn = r_guard.clone();
                Mutex::unlock(r_guard);
                return r_fn(x);
            });
        {
            let mut r_fn = r.lock().unwrap();
            *r_fn = f;
        }
        let r_guard = r.lock().unwrap();
        let r_fn = r_guard.clone();
        Mutex::unlock(r_guard);
        r_fn(0);
    }

    fn main() {
        landins_knot();
    }
} // verus!
