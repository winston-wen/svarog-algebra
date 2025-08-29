use crate::rug_seeded_rng;
use anyhow::bail;
use rug::{Integer, ops::Pow};

/// Thanks to:
/// https://github.com/GiacomoPope/ClassGroups/blob/main/classgroup_helper.py
pub fn mod_sqrt(a: impl Into<Integer>, p: impl Into<Integer>) -> Option<Integer> {
    let a: Integer = a.into();
    let p: Integer = p.into();
    let a = a.modulo(&p);
    if a.legendre(&p) == -1 {
        return None;
    }
    
    let mut s: Integer;
    if p == 2 {
        s = a.clone() % &p;
        println!("branch 2, a={}, p={}, s={}", &a, &p, &s);
    } else if &p & Integer::from(3) == 3 {
        let e = (p.clone() + 1) >> 2;
        s = a.clone().pow_mod(&e, &p).unwrap();
        println!("branch 2, a={}, p={}, s={}", &a, &p, &s);
    } else if &p & Integer::from(7) == 5 {
        // Atkin's formulas
        let e = (p.clone() - 5) >> 3;
        let a2: Integer = a.clone() * 2;
        let b = a2.clone().pow_mod(&e, &p).unwrap();
        let c = a2 * b.clone().square();
        s = &a * b * (c - 1) % &p;
        println!("branch 3, a={}, p={}, s={}", &a, &p, &s);
    } else {
        s = tonelli_shanks(&a, &p).unwrap();
        println!("branch 4, a={}, p={}, s={}", &a, &p, &s);
    }
    if s.is_even() {
        s = (-s) % p;
    }
    return Some(s);
}

/// [Cohen1993, Algorithm 1.5.1]
///
/// Thanks to:
/// https://github.com/GiacomoPope/ClassGroups/blob/main/classgroup_helper.py
pub fn tonelli_shanks(a: impl Into<Integer>, p: impl Into<Integer>) -> anyhow::Result<Integer> {
    fn reduce_prime(p: impl Into<Integer>) -> (Integer, u32) {
        let p = p.into();
        let mut q: Integer = p - 1;
        let mut e = 0;
        while q.is_even() {
            q >>= 1;
            e += 1;
        }
        return (q, e);
    }

    fn find_generator(q: impl Into<Integer>, p: impl Into<Integer>) -> Integer {
        let p: Integer = p.into();
        let q: Integer = q.into();
        let mut rng = rug_seeded_rng();
        loop {
            let n = p.clone().random_below(&mut rng);
            if n.kronecker(&p) == -1 {
                return n.pow_mod(&q, &p).unwrap();
            }
        }
    }

    fn find_exponent(b: impl Into<Integer>, p: impl Into<Integer>) -> u32 {
        let b: Integer = b.into();
        let p: Integer = p.into();
        let mut bm = b.clone();
        let mut m = 1;
        loop {
            bm = bm.pow_mod(&Integer::from(2), &p).unwrap();
            if bm == 1 {
                return m;
            }
            m += 1;
        }
    }

    // Initialize
    let a: Integer = a.into();
    let p: Integer = p.into();
    let (q, mut r) = reduce_prime(&p);
    let y = find_generator(&q, &p);
    let e = (q - 1) >> 1;
    let x = a.clone().pow_mod(&e, &p).unwrap();
    let mut b = &a * x.clone().square() % &p;
    let mut x = (a * x) % &p;

    // Find and reduce exp
    while b != 1 {
        let m = find_exponent(&b, &p);
        if m == r {
            bail!("tonelli_shanks(..) a is not a quadratic residue mod p");
        }
        let t_exp = Integer::from(2).pow(r-m-1);
        let t = y.clone().pow_mod(&t_exp, &p).unwrap();
        let y = t.clone().pow_mod(&Integer::from(2), &p).unwrap();
        r = m;
        x = x * t % &p;
        b = b * y % &p;
    }
    Ok(b)
}
