use std::{ops, u64};

use secp256k1_sys::{self as ffi, CPtr};

use crate::{CURVE_ORDER, CURVE_ORDER_WORDS, ONE, ZERO};

#[derive(Clone, Copy, Debug)]
pub struct Scalar([u8; 32]);

impl Scalar {
    #[inline]
    pub fn add(&self, other: &Scalar) -> Scalar {
        let mut x = self.clone();
        let success = unsafe {
            ffi::secp256k1_ec_seckey_tweak_add(
                ffi::secp256k1_context_no_precomp,
                x.as_mut_c_ptr(),
                other.as_c_ptr(),
            )
        };
        assert_eq!(success, 1);
        x
    }

    #[inline]
    /// $$-x = \mathtt{ord} - x$$.
    pub fn neg(&self) -> Scalar {
        let mut x = self.clone();
        unsafe {
            let success = ffi::secp256k1_ec_seckey_negate(
                ffi::secp256k1_context_no_precomp,
                x.as_mut_c_ptr(),
            );
            assert_eq!(success, 1);
        }
        x
    }

    #[inline]
    pub fn mul(&self, other: &Scalar) -> Scalar {
        let mut x = self.clone();

        let success = unsafe {
            ffi::secp256k1_ec_seckey_tweak_mul(
                ffi::secp256k1_context_no_precomp,
                x.as_mut_c_ptr(),
                other.as_c_ptr(),
            )
        };
        assert_eq!(success, 1);

        x
    }

    /// Compute $$x^{-1} \pmod n$$ in constant time.
    /// * Less side-channel leak.
    /// * Less efficient average-cases.
    #[inline]
    pub fn inv_ct(&self) -> Scalar {
        if self.eq(&ZERO) {
            return ZERO.clone();
        }
        let mut x = self.clone();

        let success = unsafe {
            ffi::secp256k1_ec_seckey_invert_ct(ffi::secp256k1_context_no_precomp, x.as_mut_c_ptr())
        };
        assert_eq!(success, 1);

        x
    }

    /// Compute $$x^{-1} \pmod n$$ in variable time.
    /// * More efficient average-cases.
    /// * More side-channel leak.
    #[inline]
    pub fn inv_vt(&self) -> Scalar {
        if self.eq(&ZERO) {
            return ZERO.clone();
        }
        let mut x = self.clone();

        let success = unsafe {
            ffi::secp256k1_ec_seckey_invert_vt(ffi::secp256k1_context_no_precomp, x.as_mut_c_ptr())
        };
        assert_eq!(success, 1);

        x
    }

    #[inline]
    pub fn new(x: i64) -> Scalar {
        let res = if x == 0 {
            ZERO.clone()
        } else if x == 1 {
            ONE.clone()
        } else if x >= 0 {
            let mut num = [0u8; 32];
            num[24..].copy_from_slice(&x.to_be_bytes());
            Scalar(num)
        } else {
            let mut num = [0u8; 32];
            num[24..].copy_from_slice(&(-x).to_be_bytes());
            Scalar(num).neg()
        };
        res
    }

    pub fn new_rand<R: rand::Rng + ?Sized>(rng: &mut R) -> Scalar {
        let mut num = [0u8; 32];
        rng.fill(&mut num);
        Scalar::new_from_be_bytes(num)
    }

    // `num` is interpreted as big-endian unsigned integer, i.e. an 256-radix positive number!
    #[inline]
    pub fn new_from_be_bytes(mut num: [u8; 32]) -> Scalar {
        if &num > &CURVE_ORDER {
            // ... then we have `num % CURVE_ORDER == num - CURVE_ORDER`.
            let x2 = u64::from_be_bytes(num[16..24].try_into().unwrap());
            let x1 = u64::from_be_bytes(num[24..32].try_into().unwrap());

            let y2 = CURVE_ORDER_WORDS[2];
            let y1 = CURVE_ORDER_WORDS[3];

            let (z1, emprunt) = soustraire_avec_emprunt(x1, y1);
            let x2 = if emprunt { x2 - 1 } else { x2 };
            let (z2, emprunt) = soustraire_avec_emprunt(x2, y2);

            // Note that x3 >= 0xFFFF_FFFF_FFFF_FFFE == y3.
            let z3 = if emprunt { 0u8 } else { 1u8 };

            num = [0u8; 32];
            num[15] = z3;
            num[16..24].copy_from_slice(&z2.to_be_bytes());
            num[24..].copy_from_slice(&z1.to_be_bytes());
        }
        Scalar(num)
    }

    #[inline]
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.clone()
    }

    #[inline]
    pub fn to_hex(&self) -> String {
        use hex::ToHex;
        self.0.encode_hex()
    }
}

impl PartialEq for Scalar {
    /// This implementation is designed to be constant time to help prevent side channel attacks.
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        let accum = self
            .0
            .iter()
            .zip(&other.0)
            .fold(0, |accum, (a, b)| accum | (a ^ b));
        unsafe { core::ptr::read_volatile(&accum) == 0 }
    }
}

impl Eq for Scalar {}

impl AsRef<[u8; 32]> for Scalar {
    /// Gets a reference to the underlying array.
    ///
    /// # Side channel attacks
    ///
    /// Using ordering functions (`PartialOrd`/`Ord`) on a reference to secret keys leaks data
    /// because the implementations are not constant time. Doing so will make your code vulnerable
    /// to side channel attacks. [`SecretKey::eq`] is implemented using a constant time algorithm,
    /// please consider using it to do comparisons of secret keys.
    #[inline]
    fn as_ref(&self) -> &[u8; 32] {
        let Scalar(dat) = self;
        dat
    }
}

impl<I> ops::Index<I> for Scalar
where
    [u8]: ops::Index<I>,
{
    type Output = <[u8] as ops::Index<I>>::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        &self.0[index]
    }
}

impl secp256k1_sys::CPtr for Scalar {
    type Target = u8;

    fn as_c_ptr(&self) -> *const Self::Target {
        let Scalar(dat) = self;
        dat.as_ptr()
    }

    fn as_mut_c_ptr(&mut self) -> *mut Self::Target {
        let &mut Scalar(ref mut dat) = self;
        dat.as_mut_ptr()
    }
}

fn soustraire_avec_emprunt(x: u64, y: u64) -> (u64, bool) {
    if y > x {
        let res = u64::MAX - y + x + 1;
        (res, true)
    } else {
        (x - y, false)
    }
}
