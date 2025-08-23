use rug::Integer;

use crate::{
    cl_elgamal::*,
    quadform::{Delta1827, TrDiscriminant},
};

#[test]
fn test_f_exp() {
    let m = Integer::from(114514);
    let g1 = Delta1827::f().exp(&m);
    let g2 = exp_f(&m);
    assert_eq!(g1, g2);
}

#[test]
fn test_encdec() {
    let m = Integer::from(-114514);

    let (x, h) = keygen();
    let ct = ClCiphertext::encrypt(&m, &h);
    let m = m.modulo(Delta1827::p());
    let m2 = ct.decrypt(&x);
    assert_eq!(m, m2);
}

#[test]
/// test linearly homomorphic encryption & decrytion.
fn test_lhe() {
    let m1 = Integer::from(-114514);
    let m2 = Integer::from(-1919);

    let (x, h) = keygen();

    '_test_add_ct: {
        let ct1 = ClCiphertext::encrypt(&m1, &h);
        let ct2 = ClCiphertext::encrypt(&m2, &h);
        let ct = ct1.add_ct(&ct2);
        let m_gt = Integer::from(&m1 + &m2).modulo(Delta1827::p());
        let m_eval = ct.decrypt(&x);
        assert_eq!(m_gt, m_eval);
    }

    '_test_add_pt: {
        let ct = ClCiphertext::encrypt(&m1, &h).add_pt(&m2);
        let m_gt = Integer::from(&m1 + &m2).modulo(Delta1827::p());
        let m_eval = ct.decrypt(&x);
        assert_eq!(m_gt, m_eval);
    }

    '_test_mul_pt: {
        let ct = ClCiphertext::encrypt(&m1, &h).mul_pt(&m2);
        let m_gt = Integer::from(&m1 * &m2).modulo(Delta1827::p());
        let m_eval = ct.decrypt(&x);
        assert_eq!(m_gt, m_eval)
    }
}

#[test]
fn test_identity() {
    let f114 = exp_f(&Integer::from(114));
    let g114 = Delta1827::generator().exp(&Integer::from(114));
    assert_eq!(f114, f114.mul(Delta1827::identity()));
    assert_eq!(g114, g114.mul(Delta1827::identity()));
}

#[test]
/// test ecdsa MtA
fn test_mta() {
    // use rug::rand::RandState;
    // let mut rng = RandState::new();
    let vji = Integer::from(Delta1827::p() - 114);
    let ki = Integer::from(Delta1827::p() - 514);
    let wj = Integer::from(Delta1827::p() - 1919);

    let (sk, pk) = keygen();
    let ki_ct = ClCiphertext::encrypt(&ki, &pk);
    // [uji] + vji == [kj] * wi
    let neg_vji = Integer::from(-&vji);
    let uji_ct = ki_ct.mul_pt(&wj).add_pt(&neg_vji);

    let uji = uji_ct.decrypt(&sk);
    let lhs = (uji + vji) % Delta1827::p();
    let rhs = (ki * wj) % Delta1827::p();
    assert_eq!(lhs, rhs);
}

#[test]
fn bench_exp() {
    use rug::Integer;
    use rug::rand::RandState;

    let mut t_ms: u128 = 0;
    let n: u128 = 100;
    for _ in 0..n {
        let mut rand = RandState::new();
        let e = Integer::from(Integer::random_bits(256, &mut rand));
        let timer = std::time::Instant::now();
        let _ = Delta1827::generator().exp(&e);
        t_ms += timer.elapsed().as_millis();
    }
    let avg = t_ms / n;
    let rem = t_ms % n;
    println!("QuadForm::exp(&self) average time on 256-bit integers: {avg}.{rem:01} ms")
}

#[test]
fn show_log2_of_order() {
    let ord_len = Delta1827::order_g().significant_bits();
    println!("{ord_len}"); // 1083
}
