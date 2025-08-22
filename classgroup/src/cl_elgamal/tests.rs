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
    let vji = p.clone().random_below(&mut rng);
    let ki = p.clone().random_below(&mut rng);
    let wj = p.clone().random_below(&mut rng);

    let (sk, pk) = keygen(&ctx);
    let ki_ct = ClCiphertext::encrypt(&ki, &pk, &ctx);
    // [uji] + vji == [kj] * wi
    let neg_vji = Integer::from(-&vji);
    let uji_ct = ki_ct.mul_pt(&wj, &ctx).add_pt(&neg_vji, &ctx);

    let uji_dec = uji_ct.decrypt(&sk, &ctx);
    let lhs = (uji_dec + vji) % ctx.p;
    let rhs = ki * wj % ctx.p;
    assert_eq!(lhs, rhs);
}
