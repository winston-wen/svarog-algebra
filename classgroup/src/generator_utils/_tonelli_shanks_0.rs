use crate::rug_seeded_rng;
use anyhow::{bail, ensure};
use rug::{Assign, Complete, Integer};

/// Straitforward impl of [Cohen1993, Algorithm 1.5.1].
#[allow(dead_code)]
pub(crate) fn tonelli_shanks_0(
    a: impl Into<Integer>,
    p: impl Into<Integer>,
) -> anyhow::Result<Integer> {
    let a: Integer = a.into();
    let p: Integer = p.into();
    let a = a % &p;
    if a == 0 {
        return Ok(a);
    }
    ensure!(
        a.legendre(&p) == 1,
        "algorithm requires `a` be a quadratic residue."
    );

    // Step 0. Find $$q, r$$ such that $$p-1 = q \cdot 2^r$$ where $$q$$ is odd.
    let mut r: u32 = 0;
    let phi_p: Integer = p.clone() - 1;
    while !phi_p.get_bit(r) {
        r += 1;
    }
    let q = phi_p >> r;

    // Step 1. Find generator.
    let mut rng = rug_seeded_rng();
    let mut n = p.random_below_ref(&mut rng).complete();
    while n.legendre(&p) != -1 {
        n.assign(p.random_below_ref(&mut rng));
    }

    // Step 2. Initialize.
    let mut y = n.clone().pow_mod(&q, &p).unwrap();
    let apow = (q.clone() - 1) >> 1;
    let x = a.clone().pow_mod(&apow, &p).unwrap();
    let mut b = (x.clone().square() * &a) % &p;
    let mut x = (x * &a) % &p;

    while b.clone().modulo(&p) != 1 {
        // Step 3. Find exponent.
        let mut m: u32 = 1;
        let mut b2m_modp = b.clone().square().modulo(&p);
        while b2m_modp != 1 {
            b2m_modp = b2m_modp.square().modulo(&p);
            m += 1;
            if m == r {
                bail!("`a` is a quadratic non-residue mod p");
            }
        }

        // Step 4. Reduce exponent.
        let ypow = Integer::from(1) << (r - m - 1);
        let t = y.clone().pow_mod(&ypow, &p).unwrap();
        y = t.clone().square().modulo(&p);
        r = m;
        x = (x * t) % &p;
        b = (b * &y) % &p;
    }

    return Ok(x);
}
