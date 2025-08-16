use curve_abstract::TrScalar;
use curve25519_dalek::Scalar as EdwardScalar;
use serde::{Deserialize, Serialize};

use crate::Curve25519;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Scalar(pub EdwardScalar);

impl TrScalar<Curve25519> for Scalar {
    fn new(n: i64) -> Self {
        let es: EdwardScalar = if n >= 0 {
            EdwardScalar::from(n as u64)
        } else {
            -EdwardScalar::from(-n as u64)
        };
        Self(es)
    }

    fn new_rand(rng: &mut (impl rand::Rng + ?Sized)) -> Self {
        let mut buf = [0u8; 64];
        rng.fill_bytes(&mut buf);
        Self::new_from_bytes(&buf)
    }

    // Little-endian, truncate or zero-padding at tail, to 64 bytes.
    fn new_from_bytes(buf: &[u8]) -> Self {
        let mut buf64 = [0u8; 64];
        let end = if buf.len() >= 64 { 64 } else { buf.len() };
        buf64[..end].copy_from_slice(&buf[..end]);
        let es = EdwardScalar::from_bytes_mod_order_wide(&buf64);
        Scalar(es)
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.0.to_bytes().to_vec()
    }

    fn add(&self, other: &Self) -> Self {
        Self(self.0 + other.0)
    }

    fn neg(&self) -> Self {
        Self(-self.0)
    }

    fn mul(&self, other: &Self) -> Self {
        Self(self.0 * other.0)
    }

    fn inv_ct(&self) -> Self {
        if self.0 == EdwardScalar::ZERO {
            Self(EdwardScalar::ZERO)
        } else {
            Self(self.0.invert())
        }
    }

    fn inv_vt(&self) -> Self {
        unimplemented!()
    }
}
