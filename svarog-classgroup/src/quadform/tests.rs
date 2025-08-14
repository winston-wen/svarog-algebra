use crate::quadform::*;

#[test]
fn test_is_reduced() {
    // Thanks to https://adrianstoll.com/post/reduced-quadratic-form-calculator/

    let form = QuadForm((1).into(), (1).into(), (1).into());
    assert_eq!(form.is_posdef(), true);
    assert_eq!(form.is_reduced(), true);

    let form = QuadForm((5).into(), (7).into(), (3).into());
    assert_eq!(form.is_posdef(), true);
    assert_eq!(form.is_reduced(), false);

    let form = QuadForm((1).into(), (1).into(), (3).into());
    assert_eq!(form.is_posdef(), true);
    assert_eq!(form.is_reduced(), true);

    let form = QuadForm((11).into(), (-6).into(), (15).into());
    assert_eq!(form.is_posdef(), true);
    assert_eq!(form.is_reduced(), true);
}

#[test]
fn test_reduce() {
    // Thanks to https://adrianstoll.com/post/reduced-quadratic-form-calculator/
    // and http://www.numbertheory.org/php/reduceneg.html

    let f = QuadForm((114).into(), (-514).into(), (1919).into());
    let f = f.reduce();
    let f0 = QuadForm((114).into(), (-58).into(), (1347).into());
    assert_eq!(f, f0);

    let f = QuadForm((114).into(), (810).into(), (1919).into());
    let f = f.reduce();
    let f0 = QuadForm((114).into(), (-102).into(), (503).into());
    assert_eq!(f, f0);

    let f = QuadForm((11).into(), (121).into(), (1331).into());
    let f = f.reduce();
    let f0 = QuadForm((11).into(), (11).into(), (1001).into());
    assert_eq!(f, f0);
}

#[test]
fn test_mul() {
    // Test Shanks' quadform composition
    // Thanks to http://www.numbertheory.org/php/composeneg.html
    // Test against posdef, primitive quadforms with discriminant -63.

    let f1 = QuadForm((9).into(), (-3).into(), (2).into());
    let id = f1.identity();
    let f3 = f1.mul(&id);
    let g3 = f1.reduce();
    assert_eq!(f3, g3);

    let f1 = QuadForm((9).into(), (-3).into(), (2).into());
    let f2 = QuadForm((2).into(), (7).into(), (14).into());
    let g3 = QuadForm((4).into(), (1).into(), (4).into());
    let f3 = f1.mul(&f2);
    assert_eq!(f3, g3);

    let f1 = QuadForm((11).into(), (5).into(), (2).into());
    let f2 = QuadForm((14).into(), (7).into(), (2).into());
    let g3 = QuadForm((1).into(), (1).into(), (16).into());
    let f3 = f1.mul(&f2);
    assert_eq!(f3, g3);

    let f1 = QuadForm((21).into(), (-20).into(), (7277).into());
    let f2 = QuadForm((114).into(), (58).into(), (1347).into());
    let g3 = QuadForm((322).into(), (-78).into(), (479).into());
    let f3 = f1.mul(&f2);
    assert_eq!(f3, g3);
}

#[test]
fn test_inv() {
    let f = QuadForm((114).into(), (514).into(), (1919).into());
    let g1 = f.square().inv();
    let g2 = f.exp(&(-2).into());

    assert_eq!(g1, g2)
}

#[test]
fn test_exp() {
    let n = 114;
    let f = QuadForm((114).into(), (514).into(), (1919).into());
    let mut g2 = f.identity();
    for _ in 0..n {
        g2 = g2.mul(&f)
    }
    let f2 = f.exp(&n.into());
    assert_eq!(f2, g2);

    let n = 1331;
    let f = QuadForm((114).into(), (514).into(), (1919).into());
    let mut g2 = f.identity();
    for _ in 0..n {
        g2 = g2.mul(&f);
    }
    let f2 = f.exp(&n.into());
    assert_eq!(f2, g2);

    let n = -1331;
    let f = QuadForm((114).into(), (514).into(), (1919).into());
    let mut g2 = f.identity();
    for _ in 0..-n {
        g2 = g2.mul(&f);
    }
    g2 = g2.inv();
    let f2 = f.exp(&n.into());
    assert_eq!(f2, g2);
}
