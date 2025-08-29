#![allow(nonstandard_style)]

use rand::RngCore;
use rug::{Integer, rand::RandState};

pub mod cl_elgamal;
pub mod generator_utils;
pub mod quadform;

/// Do NOT use `RandState::new()` directly !
/// The above usage is given by rug document, which is quite misleading.
pub fn rug_seeded_rng() -> RandState<'static> {
    let mut buf = [0u8; 32];
    let mut rng = rand::rng();
    rng.fill_bytes(&mut buf);
    let seed = Integer::from_digits(&buf, rug::integer::Order::Lsf);
    let mut rng = RandState::new();
    rng.seed(&seed);
    rng
}
