use curve_abstract::TrScalar;
use curve25519_dalek::Scalar as EdwardScalar;
use rand::RngCore;
use serde::{Deserialize, Serialize};

use crate::Curve25519;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct Scalar(pub EdwardScalar);

impl TrScalar<Curve25519> for Scalar {
    #[inline]
    fn new(n: i64) -> Self {
        let es: EdwardScalar = if n >= 0 {
            EdwardScalar::from(n as u64)
        } else {
            -EdwardScalar::from(-n as u64)
        };
        Self(es)
    }

    #[inline]
    fn new_rand() -> Self {
        let mut rng = rand::rng();
        let mut buf = [0u8; 64];
        rng.fill_bytes(&mut buf);
        Self::new_from_bytes(&buf)
    }

    // Little-endian, truncate or zero-padding at head, to 64 bytes.
    #[inline]
    fn new_from_bytes(buf: &[u8]) -> Self {
        let mut buf64 = [0u8; 64];
        let src_beg = if buf.len() >= 64 { buf.len() - 64 } else { 0 };
        let dst_beg = if buf.len() >= 64 { 0 } else { 64 - buf.len() };
        buf64[dst_beg..].copy_from_slice(&buf[src_beg..]);
        let es = EdwardScalar::from_bytes_mod_order_wide(&buf64);
        Scalar(es)
    }

    #[inline]
    fn to_bytes(&self) -> Vec<u8> {
        self.0.to_bytes().to_vec()
    }

    #[inline]
    fn add(&self, other: &Self) -> Self {
        Self(self.0 + other.0)
    }

    #[inline]
    fn sub(&self, other: &Self) -> Self {
        Self(self.0 - other.0)
    }

    #[inline]
    fn neg(&self) -> Self {
        Self(-self.0)
    }

    #[inline]
    fn mul(&self, other: &Self) -> Self {
        Self(self.0 * other.0)
    }

    #[inline]
    fn inv_ct(&self) -> Self {
        if self.0 == EdwardScalar::ZERO {
            Self(EdwardScalar::ZERO)
        } else {
            Self(self.0.invert())
        }
    }

    #[inline]
    fn inv_vt(&self) -> Self {
        unimplemented!()
    }
}
