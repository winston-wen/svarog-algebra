use std::{str::FromStr, sync::LazyLock};

use rug::{Integer, ops::Pow};

use crate::{generator_utils::sqrt_mod4p, quadform::QuadForm};

// The parameter $$p$$ is
// * secp256k1 curve order;
// * conductor of class group;
// * the exact order of ideal class $$f$$.
pub fn p() -> &'static Integer {
    static P: LazyLock<Integer> = LazyLock::new(|| {
        let digits =
            "115792089237316195423570985008687907852837564279074904382605163141518161494337";
        let res = Integer::from_str(&digits).unwrap();
        res
    });
    return &P;
}

pub fn q() -> &'static Integer {
    static Q: LazyLock<Integer> = LazyLock::new(|| {
        let p = p();
        let mut q = p.clone().square().square();
        let mut cond = false;
        while !cond {
            q = q.next_prime();

            // By [CL15, Appendix B.3] and [Kap78, p. 598], the following constraint
            // aims at minimizing the 2-Sylow subgroup of CL(-pq).
            cond = p.kronecker(&q) == -1 && q.kronecker(p) == -1;

            // The following constraint ensures that $$-pq = 1 \bmod 4$$, which
            // further ensures that $$\Delta_K = b^2 - 4ac$$ is a valid discriminant.
            cond = cond && q.clone() % 4 == 3;
        }
        return q;
    });
    return &Q;
}

// $$\Delta_k = -pq$$.
pub fn Delta_K() -> &'static Integer {
    static DELTA_K: LazyLock<Integer> = LazyLock::new(|| -(p().clone() * q()));
    return &DELTA_K;
}

// $$\Delta_p = p^2 \Delta_K$$.
pub fn Delta_p() -> &'static Integer {
    static DELTA_P: LazyLock<Integer> = LazyLock::new(|| p().clone().square() * Delta_K());
    &DELTA_P
}

pub fn f() -> &'static QuadForm {
    static F: LazyLock<QuadForm> = LazyLock::new(|| {
        let a = p().clone().square();
        let b = p().clone();
        QuadForm::new(a, b, Delta_p()).unwrap()
    });
    return &F;
}

pub fn generator_Delta_K() -> &'static QuadForm {
    static G: LazyLock<QuadForm> = LazyLock::new(|| {
        let Delta_K = Delta_K();
        let mut ra = Integer::from(2).pow(512).next_prime();
        while Delta_K.kronecker(&ra) != 1 {
            ra = ra.next_prime();
        }
        let rb = sqrt_mod4p(Delta_K, &ra).unwrap();
        let g = QuadForm::new(ra, rb, Delta_K).unwrap().square();
        return g;
    });
    return &G;
}

// This is the estimated upper bound of |G|, which is denoted as
// $$\tilde s = \lfloor \sqrt{\Delta_K} \rfloor$$ in some research papers, e.g. [CL15].
pub fn order_g_approx() -> &'static Integer {
    static ORDER_G: LazyLock<Integer> = LazyLock::new(|| Delta_K().clone().sqrt().prev_prime());
    return &ORDER_G;
}
