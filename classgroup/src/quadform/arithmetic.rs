use super::*;
use rug::Integer;

#[derive(Serialize, Deserialize, Debug, Clone, Default, PartialEq, Eq)]
pub struct QuadForm(pub Integer, pub Integer, pub Integer);

impl QuadForm {
    // Compute $$\Delta = b^2-4ac$$.
    pub fn discriminant(&self) -> Integer {
        let (a, b, c) = (&self.0, &self.1, &self.2);
        Integer::from(b ^ 2) - Integer::from(a * c) * 4
    }

    // Check if $$\gcd(a, b, c) = 1$$.
    pub fn is_primitive(&self, gcd_abc: Option<&mut Integer>) -> bool {
        let (a, b, c) = (&self.0, &self.1, &self.2);
        let mut gcd = a.clone().gcd(b);
        gcd = gcd.clone().gcd(c);
        if let Some(out) = gcd_abc {
            *out = gcd.clone();
        }
        gcd == 1
    }

    pub fn to_primitive(&self) -> QuadForm {
        let (a, b, c) = (&self.0, &self.1, &self.2);
        let mut gcd = Integer::from(1);
        let _ = self.is_primitive(Some(&mut gcd));
        QuadForm(
            a.clone() / gcd.clone(),
            b.clone() / gcd.clone(),
            c.clone() / gcd.clone(),
        )
    }

    pub fn is_posdef(&self) -> bool {
        let (a, _b, _c) = (&self.0, &self.1, &self.2);
        let delta = self.discriminant();
        &delta < &Integer::ZERO && a > &Integer::ZERO
    }

    // Check if the form is reduced.
    // Assumptions: positive definite.
    pub fn is_reduced(&self) -> bool {
        let (a, b, c) = (&self.0, &self.1, &self.2);

        let mut ret = false;
        if b <= a {
            if b >= &Integer::ZERO && a == c {
                // $$0 \le b \le a = c$$.
                ret = true;
            } else {
                // $$ -a < b \le a < c$$.
                let neg_a = -a.clone();
                if &neg_a < b && a < c {
                    ret = true;
                }
            }
        }
        ret
    }

    pub fn identity(&self) -> QuadForm {
        let delta = self.discriminant();
        let c = Integer::from(1) - delta;
        let c = c / 4;
        QuadForm(1.into(), 1.into(), c)
    }

    // [Cohen1993, Algorithm 5.4.2]
    // Given a positive definite quadratic form $$f$$, this algorithm outputs
    // the unique reduced form equivalent to $$f$$.
    pub fn reduce(&self) -> QuadForm {
        let (mut a, mut b, mut c) = (self.0.clone(), self.1.clone(), self.2.clone());

        loop {
            if {
                // Step 1. Initialize.
                let neg_a = Integer::from(-&a);
                &neg_a < &b && &b <= &a
            } {
                // Step 3.
                if &a > &c {
                    (a, b, c) = (c, -b, a);
                    /* goto Step 2. */
                } else {
                    if &a == &c && &b < &Integer::ZERO {
                        b = -b;
                    }
                    return QuadForm(a, b, c);
                }
            }

            // Step 2. Euclidean step.
            let double_a = Integer::from(&a * &Integer::from(2));
            let (mut q, mut r) = b.clone().div_rem_euc(double_a.clone());
            if &r > &a {
                r -= &double_a;
                q += 1;
            }
            c -= Integer::from(&b + &r) * &q / 2;
            b = r;
        }
    }

    // [Cohen1993, Algorithm 5.4.7] (not NUCOMP)
    // NUCOMP is [Cohen1993, Algorithm 5.4.9]
    pub fn mul(&self, other: &QuadForm) -> QuadForm {
        let (mut a1, mut b1, mut c1) = (self.0.clone(), self.1.clone(), self.2.clone());
        let (mut a2, mut b2, mut c2) = (other.0.clone(), other.1.clone(), other.2.clone());

        // Step 1. Initialize.
        #[allow(unused_assignments)]
        if &a1 > &a2 {
            (a1, a2) = (a2, a1);
            (b1, b2) = (b2, b1);
            (c1, c2) = (c2, c1);
        }
        let s = Integer::from(&b1 + &b2);
        let s: Integer = s / 2;
        let n = Integer::from(&b2 - &s);

        // Step 2. First Euclidean step.
        let (y1, d);
        if a2.clone() % a1.clone() == 0 {
            y1 = Integer::from(0);
            d = a1.clone();
        } else {
            // Solve Bezout equation such that $$x_1a_1 + y_1a_2 = d = \gcd(a_1, a_2)$$.
            (d, _, y1) = a1.clone().extended_gcd(a2.clone(), Integer::new());
        };

        // Step 3. Second Euclidean step.
        let (x2, y2, d1) = if s.clone() % d.clone() == 0 {
            (Integer::from(0), Integer::from(-1), d.clone())
        } else {
            // Solve Bezout equation such that $$x_2s - y_2d = d_1 = \gcd(s, d)$$.
            let (d1, x2, y2) = s.clone().extended_gcd(d.clone(), Integer::new());
            (x2, -y2, d1)
        };

        // Step 4. Compose.
        let v1 = Integer::from(&a1 / &d1);
        let v2 = Integer::from(&a2 / &d1);
        let r = Integer::from(&y1 * &y2) * &n - Integer::from(&x2 * &c2);

        // Equivalent to adjusting x1, y1, x2, y2 to smaller values.
        let r = Integer::from(&r % &v1);

        let a3 = Integer::from(&v1 * &v2);
        let v2r = Integer::from(&v2 * &r);
        let b3 = Integer::from(&v2r * 2) + &b2;
        let c3 = Integer::from(&c2 * &d1) + Integer::from(&b2 + &v2r) * &r;
        let c3 = Integer::from(&c3 / &v1);

        let f3 = QuadForm(a3, b3, c3);
        f3.reduce()
    }

    pub fn square(&self) -> QuadForm {
        self.mul(self)
    }

    pub fn inv(&self) -> QuadForm {
        let mut f2 = self.clone();
        f2.1 = -f2.1; // negate B.
        f2
    }

    pub fn exp(&self, k: &Integer) -> QuadForm {
        let mut base = self.clone();
        let mut res = self.identity();
        let mut expo = k.clone();

        if expo.is_negative() {
            base = self.inv();
            expo = -expo;
        }
        while expo.is_positive() {
            if expo.get_bit(0) {
                // if the least bit is 1.
                res = base.mul(&res)
            }
            base = base.square();
            expo >>= 1;
        }
        res
    }
}
