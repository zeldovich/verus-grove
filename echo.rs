use vstd::{prelude::*,invariant::*,thread::*};
use std::net::{TcpListener, TcpStream};
use std::io::{Read,Write};

verus! {

    #[verifier(external_body)]
    fn client_main() {
        println!("Running client");
        let mut stream = TcpStream::connect("127.0.0.1:12345").unwrap();
        let x = &[0,1,2,3];
        stream.write(x);
        let mut y = vec![];
        stream.read_to_end(&mut y);
        assert_eq!(x, &y[..]);
        println!("Received successful echo");
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
