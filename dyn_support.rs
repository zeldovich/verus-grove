use vstd::{prelude::*,invariant::*,thread::*};
use std::ops::Deref;

verus! {
    trait Shape {
        spec fn area_spec(&self) -> u64;

        fn area(&self) -> (ret:u64)
            ensures ret == self.area_spec()
            ;

        fn zero(&mut self)
            ensures self.area_spec() == 0
        ;
    }

    // This is one model for how `dyn Shape` could be treated by VIR/AIR. In
    // AIR (maybe even VIR?), we might not need to create a specialized
    // _Dyn_Traitname, but might be able to have a higher-order `Dyn: Trait ->
    // Type` with an axiom that `tr_bound%mymod!TraitName (Dyn tr_bound%mymod!TraitName) == true`.
    // for any trait `tr_bound%mymod!TraitName: (Dcr Type) -> Bool`.
    #[verifier(external_body)]
    struct _Dyn_Shape;

    impl _Dyn_Shape {
        #[verifier(external_body)]
        fn box_from<T:Shape>(t:T) -> Box<Self>
        {
            unimplemented!();
            //return Box::new(_Dyn_Shape{x:t});
        }
    }

    impl Shape for _Dyn_Shape {
        #[verifier(external_body)]
        spec fn area_spec(&self) -> u64;

        #[verifier(external_body)]
        fn area(&self) -> (ret:u64) { unimplemented!() }

        #[verifier(external_body)]
        fn zero(&mut self);
    }

    pub struct Triangle {
        width:u64,
    }

    pub struct Circle {
        radius:u64,
    }

    impl Shape for Triangle {
        closed spec fn area_spec(&self) -> u64 {
            (self.width/2)
        }

        fn area(&self) -> u64 {
            return self.width/2
        }

        fn zero(&mut self) {
            self.width = 0;
        }
    }

    impl Shape for Circle {
        closed spec fn area_spec(&self) -> u64 {
            self.radius
        }

        fn area(&self) -> u64 {
            return self.radius;
        }

        fn zero(&mut self) {
            self.radius = 0;
        }
    }

    fn foo_lowered<T:Shape>(t:T)
    {
        let x: Box<_Dyn_Shape>;
        x = _Dyn_Shape::box_from(t);
        let wuniquesymbol = (*x).area(); // Q: what adjustments are here?
        // let wuniquesymbol = x.area(); // Q: what adjustments are here?
    }

    fn foo<T:Shape>(t:T)
        ensures 2 == 1 + 1
    {
        // let mut x = t;
        // x.zero();
        // let z = x.area();
        // assert(z == 0u64);
        // let x: Box<dyn Shape>;
        // // x = Box::new(Triangle{width:10});
        // let wuniquesymbol = x.deref().area(); // Q: what adjustments are here?
        // let wuniquesymbol = x.area(); // Q: what adjustments are here?
        // assert(w == 5);
    }

    fn main() {
        foo(Circle{radius: 2});
        assert(true);
    }
} // verus!
