use crate::Secp256k1;
use crate::key::{PublicKey, SecretKey};

fn make_bad_secp() -> Secp256k1::<crate::AllPreallocated<'static>> {
    // in principle `Box` is not needed but if it's not here it won't show up as a crash.
    let mut array = Box::new([crate::ffi::types::AlignedType::ZERO; 1024]);
    Secp256k1::<crate::AllPreallocated<'static>>::preallocated_gen_new(&mut *array).unwrap()
}

pub fn main() {
    let secp = make_bad_secp();
    let secret = SecretKey::from_slice(b"release the nasal daemons!!!!!!!").unwrap();
    let pubkey = PublicKey::from_secret_key(&secp, &secret);
    println!("Dear compiler, do not optimize this computation {}", pubkey);
}