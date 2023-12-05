use vstd::{prelude::*,invariant::*,thread::*};
use std::net::{TcpListener, TcpStream, ToSocketAddrs};
use std::io::{Read,Write,Result};

verus! {

    // Ghost resources for network
    #[verifier(external_body)]
    pub tracked struct NetworkPointsTo {
    }

    impl NetworkPointsTo {
        spec fn chan() -> String;
        spec fn msgs() -> Set<Seq<u8>>;
    }

    // Types for network
    #[verifier(external_type_specification)]
    #[verifier(external_body)]
    pub struct ExError(std::io::Error);

    #[verifier(external_type_specification)]
    #[verifier(external_body)]
    pub struct ExTcpStream(TcpStream);


    // FIXME: will need to add ownership-related pre+post conditions to these
    // functions, which means external_fn_specification likely won't work.

    // Hoare triples for network
    #[verifier::external_fn_specification]
    pub fn ex_connect<A: ToSocketAddrs>(addr: A) -> Result<TcpStream> {
        TcpStream::connect(addr)
    }

    // Hoare triples for network

    // XXX: why are there impls `Write for &TcpStream` and `Write for TcpStream` both?
    #[verifier::external_fn_specification]
    pub fn ex_write(sf:&mut TcpStream, buf: &[u8]) -> Result<usize> {
       sf.write(buf)
    }

    #[verifier::external_fn_specification]
    pub fn ex_read(sf:&mut TcpStream, buf: &mut [u8]) -> Result<usize> {
       sf.read(buf)
    }

    #[verifier::external_fn_specification]
    pub fn ex_read_to_end(sf:&mut TcpStream, buf: &mut Vec<u8>) -> Result<usize> {
       sf.read_to_end(buf)
    }

    /*
    // FIXME: can't get this to work.
    #[verifier::external_fn_specification]
    pub fn ex_write2<'b>(sf:&mut &TcpStream, buf: &[u8]) -> Result<usize> {
       sf.write(buf)
    }
    */
    fn vec_test() {
        let mut x : std::vec::Vec<u8> = vec![];
        x.push(0);
        x.push(1);
        x.push(2);
        x.push(3);
        let y = x.as_slice();
    }

    fn client_main2(stream:&mut TcpStream) {
        // println!("Running client");
        let mut xv = vec![];
        xv.push(0);
        xv.push(1);
        xv.push(2);
        xv.push(3);

        let x : &[u8] = xv.as_slice();
        stream.write(x);
        let mut y = vec![];
        stream.read_to_end(&mut y);
        // assert_eq!(x, y.as_slice());
        // println!("Received successful echo");
    }

    #[verifier(external_body)]
    fn client_main() {
        // println!("Running client");
        let mut stream = TcpStream::connect("127.0.0.1:12345").unwrap();
        let x = &[0,1,2,3];
        stream.write(x);
        let mut y = vec![];
        stream.read_to_end(&mut y);
        assert_eq!(x, &y[..]);
        // println!("Received successful echo");
    }

    #[verifier(external_body)]
    fn server_main() {
        println!("Running server");
        let listener = TcpListener::bind("127.0.0.1:12345").unwrap();

        // could also call accept(), which the incoming Iterator wraps around.
        // https://doc.rust-lang.org/std/net/struct.TcpListener.html#method.accept
        for stream in listener.incoming() {
            let mut s = stream.unwrap();
            let mut x = [0; 128];
            let n = s.read(&mut x).unwrap();
            println!("Echoing...");
            s.write(&x[..n]);
        }
    }

    #[verifier(external_body)]
    fn main() {
        for argument in std::env::args() {
            match argument.as_str() {
                "client" => {
                    return client_main();
                }
                "server" => {
                    return server_main();
                }
                _ => {}
            }
        }
    }
} // verus!
