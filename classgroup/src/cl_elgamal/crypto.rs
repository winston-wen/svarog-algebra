use rug::Integer;
use serde::{Deserialize, Serialize};

use crate::quadform::QuadForm;

use super::cl_params;

/// Compute $$\psi: I(O_{\Delta_K}, p) \leftarrow I(O_{\Delta_p}, p)$$,
/// where $$\psi(\mathfrak{a}) = \left[\varphi^{-1}(\mathfrak{a})\right]^p
pub fn lift(gx: &QuadForm) -> QuadForm {
    let a2 = gx.a.clone();
    let double_a2 = a2.clone() * 2;
    let b2 = gx.b.clone() * cl_params::p();
    let b2 = b2 % &double_a2;
    let psi = QuadForm::new(a2, b2, cl_params::Delta_p()).unwrap();
    let psi = psi.exp(cl_params::p());
    return psi;
}

pub fn keygen() -> (Integer, QuadForm) {
    let mut rng = crate::rug_seeded_rng();
    let x = cl_params::order_g_approx().clone().random_below(&mut rng);
    let gx = cl_params::generator_Delta_K().exp(&x);
    (x, gx)
}

// The ideal class $$f = (p^2,p)$$ satisfies
// $$\mathtt{Reduce}(f^m) = (p^2, m^{-1}p)$$,
// where $$m^{-1}$$ is an odd integer such that $$ m^{-1} m \equiv 1 \pmod p$$.
// The above properties enables us to compute $$f^m$$ in $$O(1)$$ time complexity,
// bypassing the procedure of quadform composition.
pub fn exp_f(m: impl Into<Integer>) -> QuadForm {
    let m: Integer = m.into();
    let psquare = cl_params::f().a.clone();
    let m = m.clone().modulo(cl_params::p());
    if m.is_zero() {
        return QuadForm::new(1, 1, cl_params::Delta_p()).unwrap();
    }
    let mut inv_m = m.clone().invert(cl_params::p()).unwrap();
    if inv_m.is_even() {
        inv_m -= cl_params::p();
    }
    let b = inv_m * cl_params::p();
    return QuadForm::new(psquare, b, cl_params::Delta_p()).unwrap();
}

pub fn log_f(fm: &QuadForm) -> Integer {
    let inv_m = fm.b.clone() / cl_params::p();
    let m = inv_m.invert(cl_params::p());
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

pub enum Nonce<'a> {
    Automatic,
    Return(&'a mut Integer),
    Inject(&'a Integer),
}

impl ClCiphertext {
    pub fn encrypt(
        m: &Integer,
        h: &QuadForm, // other's public key
        r: Nonce,
    ) -> ClCiphertext {
        let (r, gr) = match r {
            Nonce::Automatic => keygen(),
            Nonce::Return(ret) => {
                let gr: QuadForm;
                (*ret, gr) = keygen();
                (ret.clone(), gr)
            }
            Nonce::Inject(r) => {
                let gr = cl_params::generator_Delta_K().exp(r);
                (r.clone(), gr)
            }
        };
        let hr = h.exp(&r);
        let hr = lift(&hr);
        let fm = exp_f(m);
        let hrfm = hr.mul(&fm);
        ClCiphertext { gr, hrfm }
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
