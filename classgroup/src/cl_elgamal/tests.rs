use rug::{Complete, Integer};

use crate::{
    cl_elgamal::*,
    quadform::{Delta1827bit, TrDiscriminant},
    rug_seeded_rng,
};

#[test]
fn test_f_exp() {
    let mut rng = rug_seeded_rng();
    let m = Integer::random_bits(256, &mut rng).complete();
    println!("{}", &m);
    let g1 = Delta1827bit::f().exp(&m);
    let g2 = exp_f(&m);
    assert_eq!(g1, g2);
}

#[test]
fn test_encdec() {
    let mut rng = rug_seeded_rng();
    let m = Integer::random_bits(256, &mut rng).complete();

    let (x, h) = keygen();
    let (ct, _) = ClCiphertext::encrypt(&m, &h);
    let m = m.modulo(Delta1827bit::p());
    let m2 = ct.decrypt(&x);
    assert_eq!(m, m2);
}

#[test]
/// test linearly homomorphic encryption & decrytion.
fn test_lhe() {
    let mut rng = rug_seeded_rng();
    let m1 = Integer::random_bits(256, &mut rng).complete();
    let m2 = Integer::random_bits(256, &mut rng).complete();

    let (x, h) = keygen();

    '_test_add_ct: {
        let (ct1, _) = ClCiphertext::encrypt(&m1, &h);
        let (ct2, _) = ClCiphertext::encrypt(&m2, &h);
        let ct = ct1.add_ct(&ct2);
        let m_gt = Integer::from(&m1 + &m2).modulo(Delta1827bit::p());
        let m_eval = ct.decrypt(&x);
        assert_eq!(m_gt, m_eval);
    }

    '_test_add_pt: {
        let (ct, _) = ClCiphertext::encrypt(&m1, &h);
        let ct = ct.add_pt(&m2);
        let m_gt = Integer::from(&m1 + &m2).modulo(Delta1827bit::p());
        let m_eval = ct.decrypt(&x);
        assert_eq!(m_gt, m_eval);
    }

    '_test_mul_pt: {
        let (ct, _) = ClCiphertext::encrypt(&m1, &h);
        let ct = ct.mul_pt(&m2);
        let m_gt = Integer::from(&m1 * &m2).modulo(Delta1827bit::p());
        let m_eval = ct.decrypt(&x);
        assert_eq!(m_gt, m_eval)
    }
}

#[test]
fn test_identity() {
    let mut rng = rug_seeded_rng();
    let e = Integer::from(Integer::random_bits(256, &mut rng));
    let f = exp_f(&e);
    let g = Delta1827bit::generator().exp(&e);
    assert_eq!(f, f.mul(Delta1827bit::identity()));
    assert_eq!(g, g.mul(Delta1827bit::identity()));
}

#[test]
/// test ecdsa MtA
fn test_mta() {
    let mut rng = rug_seeded_rng();
    let vji = Integer::from(Integer::random_bits(256, &mut rng));
    let ki = Integer::from(Integer::random_bits(256, &mut rng));
    let wj = Integer::from(Integer::random_bits(256, &mut rng));

    let (sk, pk) = keygen();
    let (ki_ct, _) = ClCiphertext::encrypt(&ki, &pk);
    // [uji] + vji == [kj] * wi
    let neg_vji = Integer::from(-&vji);
    let uji_ct = ki_ct.mul_pt(&wj).add_pt(&neg_vji);

    let uji = uji_ct.decrypt(&sk);
    let lhs = (uji + vji) % Delta1827bit::p();
    let rhs = (ki * wj) % Delta1827bit::p();
    assert_eq!(lhs, rhs);
}

#[test]
fn bench_exp() {
    use rug::Integer;

    let mut t_ms: u128 = 0;
    let n: u128 = 100;
    for _ in 0..n {
        let mut rand = rug_seeded_rng();
        let e = Integer::from(Integer::random_bits(256, &mut rand));
        let timer = std::time::Instant::now();
        let _ = Delta1827bit::generator().exp(&e);
        t_ms += timer.elapsed().as_millis();
    }
    let avg = t_ms / n;
    let rem = t_ms % n;
    println!("QuadForm::exp(&self) average time on 256-bit integers: {avg}.{rem:01} ms")
}

#[test]
fn show_log2_of_order() {
    let ord_len = Delta1827bit::order_g_approx().significant_bits();
    println!("{ord_len}"); // 1083
}
