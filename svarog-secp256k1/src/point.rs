use std::fmt;

use curve_abstract::{self as abs, TrCurve};
use secp256k1_sys::{self as ffi, CPtr, types::c_uint};
use serde::{Deserialize, Serialize};

use crate::{Scalar, Secp256k1, thlocal_ctx};

#[derive(Clone, PartialEq, Eq)]
pub struct Point(pub(crate) ffi::PublicKey);

impl abs::TrPoint<Secp256k1> for Point {
    #[inline]
    fn new_from_bytes(buf: &[u8]) -> Result<Self, &str> {
        Self::new_from_bytes(buf)
    }

    #[inline]
    fn to_bytes(&self) -> Vec<u8> {
        self.to_bytes33().to_vec()
    }

    #[inline]
    fn to_bytes_long(&self) -> Vec<u8> {
        self.to_bytes65().to_vec()
    }

    #[inline]
    fn add(&self, other: &Self) -> Self {
        Self::sum(&[self, other])
    }

    #[inline]
    fn sum(points: &[&Self]) -> Self {
        let mut res = Secp256k1::identity().clone();
        assert!(points.len() <= (i32::MAX as usize));
        let ptrs = {
            let mut res = Vec::new();
            for p in points {
                if *p != Secp256k1::identity() {
                    res.push(*p);
                }
            }
            res
        };
        if ptrs.len() == 0 {
            return res;
        }
        let ptrs = unsafe {
            use std::mem::transmute;
            transmute::<&[&Point], &[*const ffi::PublicKey]>(ptrs.as_ref())
        };
        let success = unsafe {
            ffi::secp256k1_ec_pubkey_combine(thlocal_ctx(), &mut res.0, ptrs.as_c_ptr(), ptrs.len())
        };
        assert_eq!(success, 1);

        res
    }

    #[inline]
    fn neg(&self) -> Self {
        let mut p = self.clone();
        unsafe {
            let success = ffi::secp256k1_ec_pubkey_negate(thlocal_ctx(), &mut p.0);
            assert_eq!(success, 1);
        }
        p
    }

    #[inline]
    fn add_gx(&self, x: &Scalar) -> Self {
        let mut p = self.clone();
        let success =
            unsafe { ffi::secp256k1_ec_pubkey_tweak_add(thlocal_ctx(), &mut p.0, x.as_c_ptr()) };
        if success == 1 {
            return p;
        } else if x == Secp256k1::zero() {
            return self.clone();
        } else if self == Secp256k1::identity() {
            return Self::new_gx(x);
        } else {
            panic!()
        }
    }

    #[inline]
    fn new_gx(x: &Scalar) -> Self {
        let mut pk = unsafe { ffi::PublicKey::new() };
        let success =
            unsafe { ffi::secp256k1_ec_pubkey_create(thlocal_ctx(), &mut pk, x.as_c_ptr()) };
        if success == 1 {
            return Self(pk);
        } else if x == Secp256k1::zero() {
            return Secp256k1::identity().clone();
        } else {
            panic!();
        }
    }

    #[inline]
    fn mul_x(&self, other: &Scalar) -> Point {
        let mut p = self.clone();
        let success = unsafe {
            ffi::secp256k1_ec_pubkey_tweak_mul(thlocal_ctx(), &mut p.0, other.as_c_ptr())
        };
        if success == 1 {
            return p;
        } else if other == Secp256k1::zero() {
            return Secp256k1::identity().clone();
        } else if self == Secp256k1::identity() {
            return Secp256k1::identity().clone();
        } else {
            panic!()
        }
    }
}

impl Serialize for Point {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.to_bytes33().to_vec().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Point {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let bytes33: Vec<u8> = Vec::<u8>::deserialize(deserializer)?;
        let point =
            Self::new_from_bytes(&bytes33).map_err(|e| serde::de::Error::custom(e.to_string()))?;
        Ok(point)
    }
}

impl Point {
    #[rustfmt::skip]
    pub(crate) const ID_BYTES33: [u8; 33] = [
        0x02,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];

    #[rustfmt::skip]
    pub(crate) const ID_BYTES65: [u8; 65] = [
        0x04,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];

    fn new_from_bytes(data: &[u8]) -> Result<Point, &'static str> {
        if data.len() != 33 && data.len() != 65 {
            return Err("Invalid length of point bytes");
        }
        let mut pk = unsafe { ffi::PublicKey::new() };
        let success = unsafe {
            ffi::secp256k1_ec_pubkey_parse(thlocal_ctx(), &mut pk, data.as_c_ptr(), data.len())
        };
        if success != 1 {
            if data.len() == 33 && data == &Self::ID_BYTES33 {
                return Ok(Secp256k1::identity().clone());
            }
            if data.len() == 65 && data == &Self::ID_BYTES65 {
                return Ok(Secp256k1::identity().clone());
            }
            return Err("Invalid point bytes (not on curve).");
        }
        Ok(Point(pk))
    }

    fn to_bytes33(&self) -> Vec<u8> {
        let mut buf = vec![0u8; 33];
        self.to_bytes_internal(&mut buf, ffi::SECP256K1_SER_COMPRESSED);
        buf
    }

    fn to_bytes65(&self) -> Vec<u8> {
        let mut buf = vec![0u8; 65];
        self.to_bytes_internal(&mut buf, ffi::SECP256K1_SER_UNCOMPRESSED);
        buf
    }

    fn to_bytes_internal(&self, ret: &mut [u8], compression: c_uint) {
        let mut n = ret.len();
        let success = unsafe {
            ffi::secp256k1_ec_pubkey_serialize(
                ffi::secp256k1_context_no_precomp,
                ret.as_mut_c_ptr(),
                &mut n,
                &self.0,
                compression,
            )
        };
        if success != 1 {
            if compression == ffi::SECP256K1_SER_COMPRESSED {
                ret.copy_from_slice(&Self::ID_BYTES33);
            } else if compression == ffi::SECP256K1_SER_UNCOMPRESSED {
                ret.copy_from_slice(&Self::ID_BYTES65);
            } else {
                panic!()
            }
        }
    }
}

impl fmt::LowerHex for Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ser = self.to_bytes65();
        for ch in &ser[1..33] {
            write!(f, "{:02x}", *ch)?;
        }
        write!(f, "_")?;
        for ch in &ser[33..] {
            write!(f, "{:02x}", *ch)?;
        }
        Ok(())
    }
}

impl fmt::Display for Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::LowerHex::fmt(self, f)
    }
}

impl fmt::Debug for Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::LowerHex::fmt(self, f)
    }
}
