use std::sync::LazyLock;

use rug::Integer;
use serde::{ Deserialize, Serialize };

use crate::quadform::{ QuadForm, TrDiscriminant };

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Default)]
struct Delta599 {}

impl TrDiscriminant for Delta599 {
    fn Delta_k() -> &'static Integer {
        todo!()
    }

    fn Delta_p() -> &'static Integer {
        static DELTA_P: LazyLock<Integer> = LazyLock::new(|| Integer::from(-599));
        &DELTA_P
    }

    fn p() -> &'static Integer {
        todo!()
    }

    fn q() -> &'static Integer {
        todo!()
    }

    fn identity() -> &'static QuadForm<Self> where Self: Sized + Clone {
        static ID: LazyLock<QuadForm<Delta599>> = LazyLock::new(|| QuadForm::new(1, 1).unwrap());
        return &ID;
    }

    fn f() -> &'static super::QuadForm<Self> where Self: Sized + Clone {
        todo!()
    }

    fn generator() -> &'static super::QuadForm<Self> where Self: Sized + Clone {
        todo!()
    }

    fn L() -> &'static Integer {
        static L: LazyLock<Integer> = LazyLock::new(|| {
            let mut val = Delta599::Delta_p().clone().abs();
            val /= 4;
            val = val.sqrt();
            val = val.sqrt();
            val
        });
        return &L;
    }

    fn order_g() -> &'static Integer {
        todo!()
    }
}

type Q = QuadForm<Delta599>;
#[test]
fn test_square() {
    let f = Q::new(12, 5).unwrap().square();
    let g = Q::new(10, 1).unwrap();
    assert_eq!(f, g);

    let f = Q::new(12, -5).unwrap().square();
    let g = Q::new(10, -1).unwrap();
    assert_eq!(f, g);

    let f = Q::new(13, 5).unwrap().square();
    let g = Q::new(10, -1).unwrap();
    assert_eq!(f, g);
}
