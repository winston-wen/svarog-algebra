use rug::{Integer, rand::RandState};
use serde::{Deserialize, Serialize};

use crate::{
    cl_elgamal::{ClSettings, derive_c_from_abd},
    quadform::QuadForm,
};

pub fn keygen(ctx: &ClSettings) -> (Integer, QuadForm) {
    let mut rng = RandState::new();
    let x = ctx.order_g.clone().random_below(&mut rng);
    let gx = ctx.g.exp(&x);
    (x, gx)
}

// The ideal class $$f = (p^2,p)$$ satisfies
// $$\mathtt{Reduce}(f^m) = (p^2, m^{-1}p)$$,
// where $$m^{-1}$$ is an odd integer such that $$ m^{-1} m \equiv 1 \pmod p$$.
// The above properties enables us to compute $$f^m$$ in $$O(1)$$ time complexity,
// bypassing the procedure of quadform composition.
pub fn exp_f(m: &Integer, ctx: &ClSettings) -> QuadForm {
    let psquare = &ctx.f.0;
    let m = m.clone().modulo(ctx.p);
    if m.is_zero() {
        return ctx.id.clone();
    }
    let mut inv_m = m.clone().invert(ctx.p).unwrap();
    if inv_m.is_even() {
        inv_m -= ctx.p;
    }
    let b = Integer::from(&inv_m * ctx.p);
    let c = derive_c_from_abd(&psquare, &b, ctx.delta_p);
    QuadForm(psquare.clone(), b, c)
}

pub fn log_f(fm: &QuadForm, ctx: &ClSettings) -> Integer {
    if fm == ctx.id {
        return Integer::new();
    }
    let inv_m = Integer::from(&fm.1 / ctx.p);
    let m = inv_m.invert(ctx.p).unwrap();
    m
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
        ctx: &ClSettings,
    ) -> ClCiphertext {
        let (r, gr) = keygen(ctx);
        let hr = h.exp(&r);
        let fm = exp_f(m, ctx);
        let hrfm = hr.mul(&fm);
        ClCiphertext { gr, hrfm }
    }

    pub fn decrypt(
        &self,
        x: &Integer, // my secret key
        ctx: &ClSettings,
    ) -> Integer {
        let h_negr = self.gr.exp(&Integer::from(-x)); // construct $$h^{-r}$$.
        let fm = self.hrfm.mul(&h_negr); // cancel $$h^r$$, homomorphicly.
        let m = log_f(&fm, ctx);
        m
    }

    pub fn add_ct(
        &self,
        other: &ClCiphertext, //
        _ctx: &ClSettings,
    ) -> ClCiphertext {
        ClCiphertext {
            gr: self.gr.mul(&other.gr),
            hrfm: self.hrfm.mul(&other.hrfm),
        }
    }

    pub fn add_pt(
        &self,
        other: &Integer, //
        ctx: &ClSettings,
    ) -> ClCiphertext {
        ClCiphertext {
            gr: self.gr.clone(),
            hrfm: self.hrfm.mul(&exp_f(other, ctx)),
        }
    }

    pub fn mul_pt(
        &self,
        other: &Integer, //
        _ctx: &ClSettings,
    ) -> ClCiphertext {
        ClCiphertext {
            gr: self.gr.exp(other),
            hrfm: self.hrfm.exp(other),
        }
    }
}
