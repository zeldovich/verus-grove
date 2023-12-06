use vstd::{prelude::*,invariant::*,thread::*};
use std::net::{TcpListener, TcpStream};
use std::io::{Read,Write};
use std::string::String;

verus! {
    // Ghost resources for network
    #[verifier(external_body)]
    pub tracked struct NetworkPointsTo {
    }

    impl NetworkPointsTo {
        spec fn chan() -> String;
        spec fn msgs() -> Set<Seq<u8>>;
    }

    // NOTE: ideally, we would give specs to the build std::net functions. There
    // are two problems:
    // (1) want to add ghost resources in pre/post conditions of these functions
    // (2) we don't want to use TCP or UDP, we want a messaging layer that does
    //     not guarantee ordering of messages but also does not limit message
    //     size, so don't really want to use either UdpSocket or TcpStream.

    // Types for network
    #[verifier(external_body)]
    pub struct Connection {
        mu:std::sync::Mutex<TcpStream>
    }

    #[verifier(external_body)]
    pub struct Listener {
        l:TcpListener
    }

    #[verifier(external_type_specification)]
    #[verifier(external_body)]
    pub struct ExString(String);

    #[verifier(external_type_specification)]
    #[verifier(external_body)]
    pub struct ExError(std::io::Error);

    impl Listener {
        #[verifier(external_body)]
        pub fn listen(addr:String) -> Result<Self, std::io::Error> {
            Ok(Listener{l: TcpListener::bind(addr)?})
        }

        #[verifier(external_body)]
        pub fn accept(&self) -> Connection {
            loop {
                match self.l.accept() {
                    Ok((stream, _addr)) => {
                        return Connection{mu: std::sync::Mutex::new(stream)}
                    }
                    Err(e) => continue
                }
            }
        }
    }

    impl Connection {
        #[verifier(external_body)]
        pub fn connect(addr:String) -> Result<Self, std::io::Error> {
            let stream = TcpStream::connect(addr)?;
            Ok(Self{mu: std::sync::Mutex::new(stream)})
        }

        #[verifier(external_body)]
        pub fn receive(&self) -> Vec<u8> {
            let mut sz_enc = [0u8; 8];
            let mut s = self.mu.lock().unwrap();
            s.read_exact(&mut sz_enc).unwrap();
            let sz = u64::from_ne_bytes(sz_enc);
            let mut msg = vec![0; sz as usize];
            s.read_exact(&mut msg).unwrap();
            msg
        }

        #[verifier(external_body)]
        pub fn send(&self, msg:&[u8]) {
            let mut sz_enc = msg.len().to_ne_bytes();
            let mut s = self.mu.lock().unwrap();
            s.write(&sz_enc).unwrap();
            s.write(msg).unwrap();
        }
    }

    // Hoare triples for network

    fn client_main(addr:String) {
        #[cfg(not(verus_keep_ghost_body))]
        println!("Running client");

        let mut maybe_conn = Connection::connect(addr);
        assume(maybe_conn.is_Ok());
        let conn = maybe_conn.unwrap();
        let mut x : Vec<u8> = Vec::new();
        x.push(0);
        x.push(1);
        x.push(2);
        x.push(3);
        conn.send(x.as_slice());
        let y = conn.receive();
        assert(x@ == y@);

        #[cfg(not(verus_keep_ghost_body))]
        {
            assert_eq!(x, &y[..]);
            println!("Received successful echo");
        }
    }

    fn server_main(addr:String) {
        #[cfg(not(verus_keep_ghost_body))]
        println!("Running server");

        let maybe_listener = Listener::listen(addr);
        assume(maybe_listener.is_Ok());
        let listener = maybe_listener.unwrap();

        loop {
            let conn = listener.accept();
            let msg = conn.receive();

            #[cfg(not(verus_keep_ghost_body))]
            println!("Echoing...");

            conn.send(msg.as_slice());
        }
    }

    #[verifier(external_body)]
    fn main() {
        let addr = "127.0.0.1:12345".to_string();
        for argument in std::env::args() {
            match argument.as_str() {
                "client" => {
                    return client_main(addr);
                }
                "server" => {
                    return server_main(addr);
                }
                _ => {}
            }
        }
    }
} // verus!
