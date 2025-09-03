use rug::Integer;
use serde::{Deserialize, Serialize};

use crate::quadform::QuadForm;

use super::delta1792;

/// Compute $$\psi: I(O_{\Delta_K}, p) \leftarrow I(O_{\Delta_p}, p)$$,
/// where $$\psi(\mathfrak{a}) = \left[\varphi^{-1}(\mathfrak{a})\right]^p
pub fn lift(gx: &QuadForm) -> QuadForm {
    let a2 = gx.a.clone();
    let double_a2 = a2.clone() * 2;
    let b2 = gx.b.clone() * delta1792::p();
    let b2 = b2 % &double_a2;
    let psi = QuadForm::new(a2, b2, delta1792::Delta_p()).unwrap();
    let psi = psi.exp(delta1792::p());
    return psi;
}

pub fn keygen() -> (Integer, QuadForm) {
    let mut rng = crate::rug_seeded_rng();
    let x = delta1792::order_g_approx().clone().random_below(&mut rng);
    let gx = delta1792::generator_Delta_K().exp(&x);
    (x, gx)
}

// The ideal class $$f = (p^2,p)$$ satisfies
// $$\mathtt{Reduce}(f^m) = (p^2, m^{-1}p)$$,
// where $$m^{-1}$$ is an odd integer such that $$ m^{-1} m \equiv 1 \pmod p$$.
// The above properties enables us to compute $$f^m$$ in $$O(1)$$ time complexity,
// bypassing the procedure of quadform composition.
pub fn exp_f(m: impl Into<Integer>) -> QuadForm {
    let m: Integer = m.into();
    let psquare = delta1792::f().a.clone();
    let m = m.clone().modulo(delta1792::p());
    if m.is_zero() {
        return QuadForm::new(1, 1, delta1792::Delta_p()).unwrap();
    }
    let mut inv_m = m.clone().invert(delta1792::p()).unwrap();
    if inv_m.is_even() {
        inv_m -= delta1792::p();
    }
    let b = inv_m * delta1792::p();
    return QuadForm::new(psquare, b, delta1792::Delta_p()).unwrap();
}

pub fn log_f(fm: &QuadForm) -> Integer {
    let inv_m = fm.b.clone() / delta1792::p();
    let m = inv_m.invert(delta1792::p());
    if m.is_ok() {
        return m.unwrap();
    } else {
        return Integer::new();
    }
}

#[derive(Serialize, Deserialize, Debug, Clone, Default, PartialEq, Eq)]
pub struct ClCiphertext {
    pub gr: QuadForm,
    pub hrfm: QuadForm,
}

impl ClCiphertext {
    pub fn encrypt(
        m: &Integer,
        h: &QuadForm, // other's public key
    ) -> (ClCiphertext, Integer) {
        let (r, gr) = keygen();
        let hr = h.exp(&r);
        let hr = lift(&hr);
        let fm = exp_f(m);
        let hrfm = hr.mul(&fm);
        (ClCiphertext { gr, hrfm }, r)
    }

    pub fn decrypt(
        &self,
        x: &Integer, // my secret key
    ) -> Integer {
        let h_negr = self.gr.exp(&Integer::from(-x)); // construct $$h^{-r}$$.
        let h_negr = lift(&h_negr);
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
