use rug::Integer;

use crate::quadform::QuadForm;

pub trait TrDiscriminant {
    fn Delta_k() -> &'static Integer;
    fn Delta_p() -> &'static Integer;
    fn p() -> &'static Integer;
    fn q() -> &'static Integer;
    fn identity() -> &'static QuadForm<Self>
    where
        Self: Sized + Clone;
    fn f() -> &'static QuadForm<Self>
    where
        Self: Sized + Clone;
    fn generator() -> &'static QuadForm<Self>
    where
        Self: Sized + Clone;
    fn L() -> &'static Integer;
    fn order_g() -> &'static Integer;
}
