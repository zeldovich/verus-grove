use vstd::{prelude::*,thread::*};
mod kv;
use kv::lmap::*;
use std::net::{TcpListener};
use std::io::{Read,Write};
// use std::thread;
// use std::time::Duration;

verus! {
    #[verifier::external_body]
    fn handle_echo(a:&[u8]) -> Vec<u8> {
        // FIXME: not supported
        return a.to_vec();
        // unimplemented!();
    }

    // FIXME: model with higher-rank trait bounds?

    // model for `dyn for<'a> Fn(&'a Args) -> Output`
    #[verifier::external_body]
    #[verifier::reject_recursive_types(Args)]
    #[verifier::reject_recursive_types(Output)]
    pub struct DynRefFn<Args: ?Sized, Output>
    {
        x:Box<dyn (for<'a> Fn((&'a Args,)) -> Output) + Sync + Send>,
    }

    impl<Args: ?Sized, Output> DynRefFn<Args, Output> {
        #[verifier::external_body]
        fn from<F:(for<'a> Fn((&'a Args,)) -> Output) + 'static + Sync + Send>(f:F) -> Self {
            return DynRefFn {
                x: Box::new(f)
            };
        }
        
        #[verifier::external_body]
        fn call(&self, args:&Args) -> Output {
            return self.x.as_ref()((args,));
        }
    }

    #[verifier::external_body]
    fn run_server(host:u64, handlers:LMap<u64, DynRefFn<[u8], Vec<u8>>>) {
        // FIXME: convert host to addr
        let addr = "127.0.0.1:12345";
        let listener = TcpListener::bind(addr).unwrap();
        let handlers: &'static _ = Box::leak(Box::new(handlers));

        loop {
            match listener.accept() {
                Ok((mut stream, _addr)) => {
                    spawn(move || {
                        let mut rpcid_enc = [0u8; 8];
                        stream.read_exact(&mut rpcid_enc).unwrap();
                        let rpcid = u64::from_ne_bytes(rpcid_enc);

                        let mut sz_enc = [0u8; 8];
                        stream.read_exact(&mut sz_enc).unwrap();
                        let sz = u64::from_ne_bytes(sz_enc);

                        let mut msg = vec![0; sz as usize];
                        stream.read_exact(&mut msg).unwrap();

                        // call RPC handler
                        handlers.get(rpcid).unwrap().call(msg.as_slice());
                    });
                }
                Err(e) => continue
            }
        }
    }
    type X = DynRefFn<[u8], Vec<u8>>;
    struct Foo<T>(T);

    fn main() {
        let handlers = LMap::<u64, Foo<X>>::new();

        // run_server(0u64, handlers); // FIXME: host

        loop {
            // FIXME: not supported
            // thread::sleep(Duration::from_millis(1_000_000_000_000_000_000));
        }
        // start server
    }
} // verus!
