use rug::{Integer, ops::Pow};

use crate::{cl_elgamal::cl_params, quadform::QuadForm, rug_seeded_rng};

#[test]
fn test_square() {
    let f = QuadForm::new(12, 5, -599).unwrap().square();
    let g = QuadForm::new(10, 1, -599).unwrap();
    assert_eq!(f, g);

    let f = QuadForm::new(12, -5, -599).unwrap().square();
    let g = QuadForm::new(10, -1, -599).unwrap();
    assert_eq!(f, g);

    let f = QuadForm::new(13, 5, -599).unwrap().square();
    let g = QuadForm::new(10, -1, -599).unwrap();
    assert_eq!(f, g);
}

#[test]
fn test_mul() {
    let a = QuadForm::new(15, 19, -599).unwrap(); // 15, 19, 16
    let b = QuadForm::new(26, 31, -599).unwrap(); // 26, 31, 15
    let c0 = QuadForm::new(6, 1, -599).unwrap(); // 6, 1, 25
    let c1 = a.mul(&b);
    let c2 = b.mul(&a);
    assert_eq!(c1, c0);
    assert_eq!(c2, c0);

    let a = QuadForm::new(34, -43, -599).unwrap(); // 34, -43, 18
    let b = QuadForm::new(20, 59, -599).unwrap(); // 20, 59, 51
    // c0 unchanged.
    let c1 = a.mul(&b);
    let c2 = b.mul(&a);
    assert_eq!(c1, c0);
    assert_eq!(c2, c0);

    let a = QuadForm::new(787, -1919, -599).unwrap(); // 787 -1919 1170
    let b = QuadForm::new(2771, -893, -599).unwrap(); // 2771 -893 72
    let c0 = QuadForm::new(3, 1, -599).unwrap(); // 3, 1, 50
    let c1 = a.mul(&b);
    let c2 = b.mul(&a);
    assert_eq!(c1, c0);
    assert_eq!(c2, c0);
}

#[test]
fn test_exp() {
    let mut rng = rug_seeded_rng();
    let g = cl_params::generator_Delta_K();
    let x = Integer::from(2)
        .pow(16)
        .random_below(&mut rng)
        .to_u64()
        .unwrap();
    let h1 = g.exp_naive(x);
    let mut h2 = g.clone();
    for _ in 1..x {
        h2 = h2.mul(g);
    }
    assert_eq!(h1, h2);
}
