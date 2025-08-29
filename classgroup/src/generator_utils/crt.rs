use rug::{Integer};

/// Chinese Remainder Theorem
///
/// Given $$x = x_i \pmod w_i$$, where $$\gcd(w_i, w_j)=1$$ for any $$i\ne j$$.
/// Solve $$x \bmod w$$, where $$w=\prod_i w_i$$.
pub fn crt(remainders: &[Integer], divisors: &[Integer]) -> Integer {
    let len = remainders.len();
    assert!(len > 0);
    let mut w = Integer::from(1);
    for i in 0..len {
        w *= &divisors[i];
    }
    let mut x = Integer::from(0);

    for i in 0..len {
        let (xi, wi) = (&remainders[i], &divisors[i]);
        let mi = w.clone() / wi;
        let mi_inv = mi.clone().invert(&wi).unwrap();
        x += xi * mi * mi_inv;
    }

    return x.modulo(&w);
}
