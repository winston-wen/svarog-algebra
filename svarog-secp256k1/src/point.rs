use std::fmt;

use erreur::*;
use secp256k1_sys::{self as ffi, CPtr, types::c_uint};

use crate::{ID, Scalar, ZERO, thlocal_ctx};

#[derive(PartialEq, Eq, Clone)]
pub struct Point(ffi::PublicKey);

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

    #[rustfmt::skip]
    pub(crate) const GENERATOR_BYTES65: [u8; 65] = [
        0x04,
        // X
        0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac,
        0x55, 0xa0, 0x62, 0x95, 0xce, 0x87, 0x0b, 0x07,
        0x02, 0x9b, 0xfc, 0xdb, 0x2d, 0xce, 0x28, 0xd9,
        0x59, 0xf2, 0x81, 0x5b, 0x16, 0xf8, 0x17, 0x98,
        // Y
        0x48, 0x3a, 0xda, 0x77, 0x26, 0xa3, 0xc4, 0x65,
        0x5d, 0xa4, 0xfb, 0xfc, 0x0e, 0x11, 0x08, 0xa8,
        0xfd, 0x17, 0xb4, 0x48, 0xa6, 0x85, 0x54, 0x19,
        0x9c, 0x47, 0xd0, 0x8f, 0xfb, 0x10, 0xd4, 0xb8
    ];

    #[inline]
    pub fn add(&self, other: &Point) -> Point {
        Self::sum(&[self, other])
    }

    #[inline]
    pub fn sum(points: &[&Point]) -> Point {
        let mut res = ID.clone();
        assert!(points.len() <= (i32::MAX as usize));
        let ptrs = {
            let mut res = Vec::new();
            for p in points {
                if ID.ne(*p) {
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
    pub fn neg(&self) -> Point {
        let mut p = self.clone();
        unsafe {
            let success = ffi::secp256k1_ec_pubkey_negate(thlocal_ctx(), &mut p.0);
            assert_eq!(success, 1);
        }
        p
    }

    #[inline]
    pub fn mul_x(&self, other: &Scalar) -> Point {
        let mut p = self.clone();
        let success = unsafe {
            ffi::secp256k1_ec_pubkey_tweak_mul(thlocal_ctx(), &mut p.0, other.as_c_ptr())
        };
        if success == 1 {
            return p;
        } else if other.eq(&ZERO) {
            return ID.clone();
        } else if self.eq(&ID) {
            return ID.clone();
        } else {
            panic!()
        }
    }

    #[inline]
    pub fn add_gx(&self, x: &Scalar) -> Point {
        let mut p = self.clone();
        let success =
            unsafe { ffi::secp256k1_ec_pubkey_tweak_add(thlocal_ctx(), &mut p.0, x.as_c_ptr()) };
        if success == 1 {
            return p;
        } else if x.eq(&ZERO) {
            return self.clone();
        } else if self.eq(&ID) {
            return Point::new_gx(x);
        } else {
            panic!()
        }
    }

    #[inline]
    pub(crate) fn new_identity() -> Point {
        Point(unsafe { ffi::PublicKey::new() })
    }

    #[inline]
    pub(crate) fn new_generator() -> Point {
        Point::new_from_bytes(&Self::GENERATOR_BYTES65).unwrap()
    }

    #[inline]
    pub fn new_gx(x: &Scalar) -> Point {
        let mut pk = unsafe { ffi::PublicKey::new() };
        let success =
            unsafe { ffi::secp256k1_ec_pubkey_create(thlocal_ctx(), &mut pk, x.as_c_ptr()) };
        if success == 1 {
            return Point(pk);
        } else if x.eq(&ZERO) {
            return ID.clone();
        } else {
            panic!();
        }
    }

    pub fn new_from_bytes(data: &[u8]) -> Resultat<Point> {
        assert_throw!(data.len() == 33 || data.len() == 65);
        let mut pk = unsafe { ffi::PublicKey::new() };
        let success = unsafe {
            ffi::secp256k1_ec_pubkey_parse(thlocal_ctx(), &mut pk, data.as_c_ptr(), data.len())
        };
        if success != 1 {
            if data.len() == 33 && data == &Self::ID_BYTES33 {
                return Ok(ID.clone());
            }
            if data.len() == 65 && data == &Self::ID_BYTES65 {
                return Ok(ID.clone());
            }
            throw!("", "Invalid point bytes");
        }
        Ok(Point(pk))
    }

    pub fn to_bytes33(&self) -> Vec<u8> {
        let mut buf = vec![0u8; 33];
        self.to_bytes_internal(&mut buf, ffi::SECP256K1_SER_COMPRESSED);
        buf
    }

    pub fn to_bytes65(&self) -> Vec<u8> {
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

    pub fn to_hex33(&self) -> String {
        use hex::ToHex;
        self.to_bytes33().encode_hex()
    }

    pub fn to_hex65(&self) -> String {
        use hex::ToHex;
        self.to_bytes65().encode_hex()
    }
}

impl fmt::LowerHex for Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ser = self.0.underlying_bytes();
        for ch in &ser[..] {
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
