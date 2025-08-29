use anyhow::{ bail, ensure };
use rug::{ Integer };

use super::crt;

pub fn sqrt_mod4p(a: impl Into<Integer>, p: impl Into<Integer>) -> anyhow::Result<Integer> {
    let a: Integer = a.into();
    let p: Integer = p.into();
    let p4 = p.clone() * 4;
    let a = a.modulo(&p4);
    if a == 0 {
        return Ok(a);
    }

    let a_mod4 = a.clone() % 4;
    if a_mod4 < 2 {
        let mut res_mod4_vec = Vec::new();
        if a_mod4 == 0 {
            res_mod4_vec.push(Integer::from(0));
        } else {
            res_mod4_vec.push(Integer::from(1));
            res_mod4_vec.push(Integer::from(3));
        }

        let res_modp = sqrt_modp(&a, &p).unwrap();
        let res_modp_vec = if res_modp == 0 {
            vec![res_modp]
        } else {
            vec![p.clone() - &res_modp, res_modp]
        };

        let divisors = vec![Integer::from(4), p.clone()];

        let mut res_vec = Vec::new();
        for i in 0..res_mod4_vec.len() {
            for j in 0..res_modp_vec.len() {
                let res_mod4 = res_mod4_vec[i].clone();
                let res_modp = res_modp_vec[j].clone();
                let res = crt(&[res_mod4, res_modp], &divisors);
                res_vec.push(res);
            }
        }
        res_vec.sort();

        return Ok(res_vec[0].clone());
    } else {
        bail!("a is a quadratic non-residue mod 4.");
    }
}

/// Thanks to:
/// https://github.com/GiacomoPope/ClassGroups/blob/main/classgroup_helper.py
pub fn sqrt_modp(a: impl Into<Integer>, p: impl Into<Integer>) -> anyhow::Result<Integer> {
    let a: Integer = a.into();
    let p: Integer = p.into();
    let a = a.modulo(&p);
    if a == 0 {
        return Ok(a);
    }
    ensure!(a.legendre(&p) == 1, "algorithm requires `a` be a quadratic residue.");

    let mut s: Integer;
    if p == 2 {
        s = a.clone().modulo(&p);
    } else if (&p & Integer::from(3)) == 3 {
        let e = (p.clone() + 1) >> 2;
        s = a.clone().pow_mod(&e, &p).unwrap();
    } else if (&p & Integer::from(7)) == 5 {
        // Atkin's formulas
        let e = (p.clone() - 5) >> 3;
        let a2: Integer = a.clone() * 2;
        let b = a2.clone().pow_mod(&e, &p).unwrap();
        let c = a2 * b.clone().square();
        s = (&a * b * (c - 1)) % &p;
    } else {
        s = tonelli_shanks(&a, &p);
    }
    if s.is_even() {
        s = &p - s;
    }
    return Ok(s);
}

/// Rust impl of this python snippet:
///
/// https://www.ctfrecipes.com/cryptography/general-knowledge/maths/modular-arithmetic/tonelli-shanks
fn tonelli_shanks(a: impl Into<Integer>, p: impl Into<Integer>) -> Integer {
    let a: Integer = a.into();
    let p: Integer = p.into();
    let a = a.modulo(&p);

    // Step 0. Find $$q, r$$ such that $$p-1 = q \cdot 2^r$$ where $$q$$ is odd.
    let mut s: u32 = 0;
    let q: Integer = p.clone() - 1;
    while !q.get_bit(s) {
        s += 1;
    }
    let q = q >> s;

    if s == 1 {
        let pow = (p.clone() + 1) >> 2;
        let x = a.pow_mod(&pow, &p).unwrap();
        return x;
    }

    let z = {
        let mut z = Integer::from(2);
        while z.legendre(&p) != -1 {
            z += 1;
        }
        z
    };

    let mut c = z.clone().pow_mod(&q, &p).unwrap();
    let mut r = a
        .clone()
        .pow_mod(&((q.clone() + 1) >> 1), &p)
        .unwrap();
    let mut t = a.clone().pow_mod(&q, &p).unwrap();

    let mut m = s as i32;

    while (t.clone() - 1) % &p != 0 {
        let mut t2 = t.clone().square().modulo(&p);
        let mut i: i32 = 0;
        for j in 1..m {
            i = j;
            if (t2.clone() - 1) % &p == 0 {
                break;
            }
            t2 = t2.square().modulo(&p);
        }

        let b = c
            .clone()
            .pow_mod(&Integer::from(1 << (m - i - 1)), &p)
            .unwrap();
        r = (r * &b).modulo(&p);
        c = b.square().modulo(&p);
        t = (t * &c).modulo(&p);
        m = i;
    }

    return r;
}
