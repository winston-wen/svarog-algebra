use std::fmt::Debug;

use serde::{Deserialize, Serialize};

pub trait TrCurve: Sized {
    type PointT: TrPoint<Self>;
    type ScalarT: TrScalar<Self>;

    fn curve_order() -> &'static [u8];
    fn field_order() -> &'static [u8];
    fn generator() -> &'static Self::PointT;
    fn identity() -> &'static Self::PointT;
    fn zero() -> &'static Self::ScalarT;
    fn one() -> &'static Self::ScalarT;
}

#[rustfmt::skip]
pub trait TrScalar<C: TrCurve>: 
    Clone + Debug + PartialEq + Eq + Send + Sync +
    Serialize + for<'de> Deserialize<'de>
{
    fn new(n: i64) -> Self;
    fn new_rand() -> Self;
    fn new_from_bytes(buf: &[u8]) -> Self;
    fn to_bytes(&self) -> Vec<u8>;

    fn add(&self, other: &Self) -> Self;
    fn neg(&self) -> Self;
    fn sub(&self, other: &Self) -> Self;
    fn mul(&self, other: &Self) -> Self;
    fn inv_ct(&self) -> Self;
    fn inv_vt(&self) -> Self;
}

#[rustfmt::skip]
pub trait TrPoint<C: TrCurve>:
    Clone + Debug + PartialEq + Eq + Send + Sync +
    Serialize + for<'de> Deserialize<'de>
{
    fn new_from_bytes(buf: &[u8]) -> Result<Self, &str>;
    fn to_bytes(&self) -> Vec<u8>;
    fn to_bytes_long(&self) -> Vec<u8>;
    
    fn add(&self, other: &Self) -> Self;
    fn sum(points: &[&Self]) -> Self;
    fn neg(&self) -> Self;
    fn sub(&self, other: &Self) -> Self;
    fn add_gx(&self, x: &C::ScalarT) -> Self;
    fn sub_gx(&self, x: &C::ScalarT) -> Self;
    fn new_gx(x: &C::ScalarT) -> Self;
    fn mul_x(&self, x: &C::ScalarT) -> Self;
}
