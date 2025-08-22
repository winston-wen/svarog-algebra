use rug::{Integer, ops::Pow};

use crate::cl_elgamal::{setup_1827bit::CTX as ctx, *};

#[test]
fn test_f_exp() {
    let m = Integer::from(114514);
    let g1 = ctx.f.exp(&m);
    let g2 = exp_f(&m, &ctx);
    assert_eq!(g1, g2);
}

#[test]
fn test_encdec() {
    let m = Integer::from(-114514);

    let (x, h) = keygen(&ctx);
    let ct = ClCiphertext::encrypt(&m, &h, &ctx);
    let m = m.modulo(ctx.p);
    let m2 = ct.decrypt(&x, &ctx);
    assert_eq!(m, m2);
}

#[test]
/// test linearly homomorphic encryption & decrytion.
fn test_lhe() {
    let m1 = Integer::from(-114514);
    let m2 = Integer::from(-1919);

    let (x, h) = keygen(&ctx);

    '_test_add_ct: {
        let ct1 = ClCiphertext::encrypt(&m1, &h, &ctx);
        let ct2 = ClCiphertext::encrypt(&m2, &h, &ctx);
        let ct = ct1.add_ct(&ct2, &ctx);
        let m_gt = Integer::from(&m1 + &m2).modulo(ctx.p);
        let m_eval = ct.decrypt(&x, &ctx);
        assert_eq!(m_gt, m_eval)
    }

    '_test_add_pt: {
        let ct = ClCiphertext::encrypt(&m1, &h, &ctx).add_pt(&m2, &ctx);
        let m_gt = Integer::from(&m1 + &m2).modulo(ctx.p);
        let m_eval = ct.decrypt(&x, &ctx);
        assert_eq!(m_gt, m_eval)
    }

    '_test_mul_pt: {
        let ct = ClCiphertext::encrypt(&m1, &h, &ctx).mul_pt(&m2, &ctx);
        let m_gt = Integer::from(&m1 * &m2).modulo(ctx.p);
        let m_eval = ct.decrypt(&x, &ctx);
        assert_eq!(m_gt, m_eval)
    }
}

#[test]
/// test ecdsa MtA
fn test_mta() {
    use rug::rand::RandState;
    let mut rng = RandState::new();
    let p: Integer = Integer::from(2).pow(251) - 1;
    let v21 = p.clone().random_below(&mut rng);
    let k1 = p.clone().random_below(&mut rng);
    let w2 = p.clone().random_below(&mut rng);

    let (sk1, pk1) = keygen(&ctx);
    let k1_ct = ClCiphertext::encrypt(&k1, &pk1, &ctx);
    // [u21] + v21 == [k1] * w2
    let neg_v21 = Integer::from(-&v21);
    let u21_ct = k1_ct.mul_pt(&w2, &ctx).add_pt(&neg_v21, &ctx);

    let u21_dec = u21_ct.decrypt(&sk1, &ctx);
    let lhs = u21_dec + v21;
    let rhs = k1 * w2 % ctx.p;
    assert_eq!(lhs, rhs);
}
