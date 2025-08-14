mod crypto;
pub mod setup_1827bit;

pub use crypto::*;
use rug::Integer;

use crate::quadform::QuadForm;

pub fn derive_c_from_abd(a: &Integer, b: &Integer, delta: &Integer) -> Integer {
    (b.clone().square() - delta.clone()) / 4 / a.clone()
}

pub struct ClSettings {
    pub p: &'static Integer,
    pub q: &'static Integer,
    pub delta_k: &'static Integer,
    pub delta_p: &'static Integer,
    pub g: &'static QuadForm,
    pub f: &'static QuadForm,
    pub order_g: &'static Integer,
    pub id: &'static QuadForm, // a.k.a. the principal ideal class.
}

#[cfg(test)]
mod tests;
