use rug::{Integer, rand::RandState};
use serde::{Deserialize, Serialize};

use crate::quadform::{Delta1827, QuadForm, TrDiscriminant};

pub fn keygen() -> (Integer, QuadForm<Delta1827>) {
    let mut rng = RandState::new();
    let x = Delta1827::order_g().clone().random_below(&mut rng);
    let gx = Delta1827::generator().exp(&x);
    (x, gx)
}

// The ideal class $$f = (p^2,p)$$ satisfies
// $$\mathtt{Reduce}(f^m) = (p^2, m^{-1}p)$$,
// where $$m^{-1}$$ is an odd integer such that $$ m^{-1} m \equiv 1 \pmod p$$.
// The above properties enables us to compute $$f^m$$ in $$O(1)$$ time complexity,
// bypassing the procedure of quadform composition.
pub fn exp_f(m: &Integer) -> QuadForm<Delta1827> {
    let psquare = Delta1827::f().a.clone();
    let m = m.clone().modulo(Delta1827::p());
    if m.is_zero() {
        return Delta1827::identity().clone();
    }
    let mut inv_m = m.clone().invert(Delta1827::p()).unwrap();
    if inv_m.is_even() {
        inv_m -= Delta1827::p();
    }
    let b = inv_m * Delta1827::p();
    QuadForm::new(psquare, b)
}

pub fn log_f(fm: &QuadForm<Delta1827>) -> Integer {
    let inv_m = fm.b.clone() / Delta1827::p();
    let m = inv_m.invert(Delta1827::p());
    if m.is_ok() {
        return m.unwrap();
    } else {
        return Integer::new();
    }
}

#[derive(Serialize, Deserialize, Debug, Clone, Default, PartialEq, Eq)]
pub struct ClCiphertext {
    pub gr: QuadForm<Delta1827>,
    pub hrfm: QuadForm<Delta1827>,
}

impl ClCiphertext {
    pub fn encrypt(
        m: &Integer,
        h: &QuadForm<Delta1827>, // other's public key
    ) -> ClCiphertext {
        let (r, gr) = keygen();
        let hr = h.exp(&r);
        let fm = exp_f(m);
        let hrfm = hr.mul(&fm);
        ClCiphertext { gr, hrfm }
    }

    pub fn decrypt(
        &self,
        x: &Integer, // my secret key
    ) -> Integer {
        let h_negr = self.gr.exp(&Integer::from(-x)); // construct $$h^{-r}$$.
        let fm = self.hrfm.mul(&h_negr); // cancel $$h^r$$, homomorphicly.
        let m = log_f(&fm);
        m
    }

    pub fn add_ct(
        &self,
        other: &ClCiphertext, //
    ) -> ClCiphertext {
        ClCiphertext {
            gr: self.gr.mul(&other.gr),
            hrfm: self.hrfm.mul(&other.hrfm),
        }
    }

    pub fn add_pt(
        &self,
        other: &Integer, //
    ) -> ClCiphertext {
        ClCiphertext {
            gr: self.gr.clone(),
            hrfm: self.hrfm.mul(&exp_f(other)),
        }
    }

    pub fn mul_pt(
        &self,
        other: &Integer, //
    ) -> ClCiphertext {
        ClCiphertext {
            gr: self.gr.exp(other),
            hrfm: self.hrfm.exp(other),
        }
    }
}
