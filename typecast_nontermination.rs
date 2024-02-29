#![feature(min_specialization)]

trait Term {
    fn is_lambda_abstraction() -> bool;
    fn call(Term) -> Term;
    // requires is_lambda_abstraction
}

pub TermExpr {
    Box<dyn Term>
}

fn ap(x:Box<dyn Term>, y:Box<dyn Term>) -> Box<dyn Term> {
    if x.is_lambda_abstraction() {
        y.call(y)
    } else {
        
    }
}

// [λ x, ap(x,x)]
fn lambda(x:&dyn Term) -> &dyn Term {
    // corresponds to the term [ap(x,x)]
}

fn cast<A,B>(e1:B,e2:A) -> B {
    unimplemented!()
}

trait Dtrait {
    fn call<A>(A) -> A;
}
type D := dyn Dtrait;

// type X = dyn (trait {
//     type A;
//     fn call(a: Self::A) -> Self::A;
// })

fn main() {}
