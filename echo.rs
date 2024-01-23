use vstd::{prelude::*,invariant::*};
// use vstd::string::new_strlit;
use std::net::{TcpListener, TcpStream};
use std::io::{Read,Write};
use std::string::String;

verus! {
    // Ghost resources for network
    #[verifier(external_body)]
    pub tracked struct NetworkPointsTo {
    }

    pub ghost struct Message {
        pub data: Seq<u8>,
        pub sender: String,
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

    pub trait AtomicUpdate<Ag, At, Rg, Rt> {
        spec fn requires(&self, ag:Ag, at:At) -> bool;
        spec fn ensures(&self, ag:Ag, at:At, rg:Rg, rt:Rt) -> bool;
        proof fn call_once(tracked self, ag:Ag, tracked at:At) -> (tracked r:(Ghost<Rg>, Tracked<Rt>)) where Self: std::marker::Sized
            requires self.requires(ag, at)
            ensures self.ensures(ag, at, r.0@, r.1@);
            // opens_invariants any
    }

    trait iPred<X> {
        spec fn get_parameter() -> X;
    }

    // Hoare triples for network
    impl Connection<P: iPred<(String, Set<Message>)>> {
        pub spec fn local(self) -> String;
        pub spec fn remote(self) -> String;

        #[verifier(external_body)]
        pub fn connect(addr:String) -> Result<Self, std::io::Error> {
            let stream = TcpStream::connect(addr)?;
            Ok(Self{mu: std::sync::Mutex::new(stream)})
        }

        // Iris: (P self.local msg) ={⊤}=∗ P self.local msg ∗ (∀ m, m ∈ msg → Φ m))
        // ⤳[uncurry]
        // Here: (∀ m msg, P self.local msg ∗ ⌜m ∈ msg⌝ ={⊤}=∗ P self.local msg ∗ Φ m)
        #[verifier(external_body)]
        pub fn receive<Phi, Au:AtomicUpdate<Message, NetworkPointsTo, (), (NetworkPointsTo, Phi)>>
            (&self, au:Tracked<Au>)
                       -> (ret:(Vec<u8>, Tracked<Phi>))
            (
                forall |msg:_, netptsto:_|
                (netptsto@.msgs().contains(Message{
                    data:data@,
                    sender: self.remote(),
                })) ==> #[trigger] au.requires(msg, netptsto)
            ),
            (
                forall |ag:_, at:_, at2:_|
                (#[trigger] au.ensures(ag, at, (), at2)) ==> (at2 == at)
            ),

            ensures ({
                let (data, phi) = ret;
                netptsto2@ == netptsto@ &&
                netptsto@.msgs().contains(Message{
                    data:data@,
                    sender: self.remote(),
                })
            })
        {
            let mut sz_enc = [0u8; 8];
            let mut s = self.mu.lock().unwrap();
            s.read_exact(&mut sz_enc).unwrap();
            let sz = u64::from_ne_bytes(sz_enc);
            let mut msg = vec![0; sz as usize];
            s.read_exact(&mut msg).unwrap();
            return (msg, Tracked::assume_new())
        }

        #[verifier(external_body)]
        pub fn send(&self, msg:&[u8], netptsto:Tracked<NetworkPointsTo>)
                    -> (ret:Tracked<NetworkPointsTo>)
            requires netptsto@.host() == self.remote()
            ensures ({
                let netptsto2 = ret;
                netptsto2@.host() == netptsto@.host() &&
                netptsto2@.msgs() == netptsto@.msgs().insert(Message{
                    data: msg@,
                    sender: self.local()
                })
            })
        {
            let mut sz_enc = msg.len().to_ne_bytes();
            let mut s = self.mu.lock().unwrap();
            s.write(&sz_enc).unwrap();
            s.write(msg).unwrap();
            return Tracked::assume_new();
        }
    }

    fn client_main(addr:String, tracked netptsto:NetworkPointsTo) {
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
        let Tracked(netptsto) = conn.send(x.as_slice(), Tracked(netptsto));
        let (y, netptsto) = conn.receive(Tracked(netptsto));
        assert(x@ == y@);

        #[cfg(not(verus_keep_ghost_body))]
        {
            assert_eq!(x, &y[..]);
            println!("Received successful echo");
        }
    }

    fn server_main(addr:String, tracked netptsto:NetworkPointsTo) {
        #[cfg(not(verus_keep_ghost_body))]
        println!("Running server");

        let maybe_listener = Listener::listen(addr);
        assume(maybe_listener.is_Ok());
        let listener = maybe_listener.unwrap();

        let tracked mut netptsto = netptsto;
        loop {
            let conn = listener.accept();
            let (msg, Tracked(netptsto2)) = conn.receive(Tracked(netptsto));
            proof { netptsto = netptsto2; }

            #[cfg(not(verus_keep_ghost_body))]
            println!("Echoing...");

            let Tracked(netptsto2) = conn.send(msg.as_slice(), Tracked(netptsto));
            proof { netptsto = netptsto2; }
        }
    }

    #[verifier(external_body)]
    fn main() {
        /*
        // FIXME: can't seem to have any string literals in verified code....
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
        */
    }
} // verus!
