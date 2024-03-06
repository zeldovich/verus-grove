use vstd::{prelude::*,thread::*};
mod kv;
use kv::*;

verus! {
#[verifier(external_body)]
pub struct GhostToken;

#[verifier(external_body)]
pub struct GhostWitness;

pub trait SessionType {
    // type DualType : SessionType;
}


#[verifier(external_body)]
pub struct SessionId<#[verifier::reject_recursive_types] T> {
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

pub struct SessEnd {
}

impl<T,S:SessionType> SessionType for SessSharedSend<T,S> {
    type DualType = SessReceive<T,S::DualType>;
}
impl<T,S:SessionType> SessionType for SessSend<T,S> {
    type DualType = SessReceive<T,S::DualType>;
}
impl<T,S:SessionType> SessionType for SessReceive<T,S> {
    type DualType = SessSend<T,S::DualType>;
}
impl SessionType for SessEnd {
    type DualType = SessEnd;
}

#[verifier(external_body)]
pub struct Channel<#[verifier::reject_recursive_types] T:SessionType> {
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
    let (tok, ch2) = ch.Receive();
    let ch2 = ch2.Send(ptsto);
    let (ptsto_new, ch2) = ch2.Receive();
    // let client_ch = MakeSess();

    loop {
        let (tok2, ch) = ch.Receive();
        assert(false); // based on tok and tok2
    }
}

pub fn main() {}

}
