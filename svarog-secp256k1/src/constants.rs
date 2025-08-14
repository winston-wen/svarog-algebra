use std::{cell::RefCell, sync::LazyLock};

use crate::{Context, Point, Scalar};

use secp256k1_sys as ffi;

/// The Prime for the secp256k1 field element.
#[rustfmt::skip]
pub const FIELD_SIZE: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xfe, 0xff, 0xff, 0xfc, 0x2f
];

/// The order of the secp256k1 curve.
#[rustfmt::skip]
pub const CURVE_ORDER: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
    0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b,
    0xbf, 0xd2, 0x5e, 0x8c, 0xd0, 0x36, 0x41, 0x41
];

#[rustfmt::skip]
pub(crate) const CURVE_ORDER_WORDS: [u64; 4] = [
    0xFFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFE,
    0xBAAE_DCE6_AF48_A03B, 0xBFD2_5E8C_D036_4141
];

#[rustfmt::skip]
pub static ZERO: LazyLock<Scalar> = LazyLock::new(|| Scalar::new_from_be_bytes([0u8; 32]));
#[rustfmt::skip]
pub static ONE: LazyLock<Scalar> = LazyLock::new(|| Scalar::new_from_be_bytes([
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
]));
pub static ID: LazyLock<Point> = LazyLock::new(|| Point::new_identity());
pub static GEN: LazyLock<Point> = LazyLock::new(|| Point::new_generator());

thread_local! {
    static CTX: RefCell<Option<Context>> = RefCell::new(None);
}

pub fn thlocal_ctx() -> *const ffi::Context {
    CTX.with(|obj| {
        let mut instance = obj.borrow_mut();
        if instance.is_none() {
            *instance = Some(Context::new())
        }
        instance.as_ref().unwrap().0.as_ptr()
    })
}
