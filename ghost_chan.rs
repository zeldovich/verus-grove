use vstd::{prelude::*,thread::*};
mod kv;
use kv::*;

verus! {
#[verifier(external_body)]
pub struct GhostToken;

#[verifier(external_body)]
pub struct GhostWitness;

pub trait DualType {
    type DualType : SessionType;
}

pub trait SessionType /* : DualType */ {
    // type DualType : SessionType;
}

#[verifier(external_body)]
#[verifier::reject_recursive_types(T)]
pub struct SessionId<T> {
    _unused:std::marker::PhantomData<T>
}

// TODO: mathematical predicate
pub struct SessSend<T, S:SessionType> {
    _unused1:std::marker::PhantomData<T>,
    _unused2:std::marker::PhantomData<S>,
}

pub struct SessSharedSend<T, S:SessionType> {
    _unused1:std::marker::PhantomData<T>,
    _unused2:std::marker::PhantomData<S>,
}

pub struct SessReceive<T, S:SessionType> {
    _unused1:std::marker::PhantomData<T>,
    _unused2:std::marker::PhantomData<S>,
}

pub struct SessSharedReceive<T, S:SessionType> {
    _unused1:std::marker::PhantomData<T>,
    _unused2:std::marker::PhantomData<S>,
}


pub struct SessEnd {
}

// impl<T,S:SessionType> DualType for SessSharedSend<T,S> {
//     type DualType = SessReceive<T, S::DualType>;
// }
impl<T,S:SessionType> SessionType for SessSharedSend<T,S> {}

// impl<T,S:SessionType> DualType for SessSend<T,S> {
//     type DualType = SessReceive<T, S::DualType>;
// }
impl<T,S:SessionType> SessionType for SessSend<T,S> {
}

// impl<T,S:SessionType> DualType for SessReceive<T,S> {
//     type DualType = SessSend<T, S::DualType>;
// }
impl<T,S:SessionType> SessionType for SessReceive<T,S> {
}

// impl DualType for SessEnd {
//     type DualType = SessEnd;
// }
impl SessionType for SessEnd {
}

#[verifier(external_body)]
#[verifier::reject_recursive_types(T)]
pub struct Channel<T:SessionType> {
    _unused:std::marker::PhantomData<T>
}

type PutEscrow =
        &'static SessSharedSend<GhostToken,
        SessReceive<GhostMapPointsTo<u64,u64>,
        SessSend<GhostMapPointsTo<u64,u64>,
        SessReceive<&'static SessSharedSend<GhostToken,
                                   SessReceive<GhostMapPointsTo<u64,u64>, SessEnd>>, SessEnd>>>>;

type CoPutEscrow =
        SessReceive<GhostToken,
        SessSend<GhostMapPointsTo<u64,u64>,
        SessReceive<GhostMapPointsTo<u64,u64>,
        SessSend<&'static SessSharedSend<GhostToken,
                                SessReceive<GhostMapPointsTo<u64,u64>, SessEnd>>, SessEnd>>>>;

impl<T,S:SessionType> SessSend<T, S> {
    #[verifier(external_body)]
    fn Send(self, t:T) -> S {
        unimplemented!();
    }
}

impl<T,S:SessionType> SessReceive<T, S> {
    #[verifier(external_body)]
    fn Receive(self) -> (T, S) {
        unimplemented!();
    }
}

impl<T,S:SessionType> SessSharedSend<T, S> {
    /*
    #[verifier(external_body)]
    fn new() -> {
        
    }*/

    #[verifier(external_body)]
    fn Send(&self, t:T) -> S {
        unimplemented!();
    }
}

impl<T,S:SessionType> SessSharedReceive<T, S> {
    #[verifier(external_body)]
    fn Send(&self, t:T) -> S {
        unimplemented!();
    }
}

// FIXME: can't put opens_invariant on this
/*
impl<T,S:SessionType> Drop for SessSharedReceive<T, S> {
    #[verifier(external_body)]
    #[cfg_attr(feature = "compile_error", no_panic::no_panic)]
    fn drop(&mut self)
        // opens_invariant none
    {
        // Avoid double panic when we are already panicking
        panic!("linear type dropped")
    }
}*/

// Rule: drop must NEVER be called on any Sess
pub fn server_handle_put(ch:PutEscrow, tok:GhostToken) {
    // XXX: making this Send call should create an obligation to get to the end
    // of the channel in order to close the masks.
    let ch = ch.Send(tok);
    let (ptsto, ch) = ch.Receive();
    // do stuff with ptsto
    let ch = ch.Send(ptsto);
    let (client_ch, ch) = ch.Receive();
}

pub fn start_escrow_handler(ch:CoPutEscrow, ptsto:GhostMapPointsTo<u64, u64>) {
    // FIXME: use SharedReceive
    let (tok, ch2) = ch.Receive();
    let ch2 = ch2.Send(ptsto);
    let (ptsto_new, ch2) = ch2.Receive();
    // let client_ch = MakeSess();

    loop {
        let (tok2, _) = ch.Receive();
        assert(false); // based on tok and tok2
    }
}

pub fn main() {}

}
