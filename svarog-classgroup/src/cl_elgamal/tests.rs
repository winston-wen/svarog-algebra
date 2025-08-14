use rug::Integer;

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
