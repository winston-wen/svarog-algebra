use std::marker::PhantomData;

use super::*;
use rug::Integer;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, Clone, Default, PartialEq, Eq)]
pub struct QuadForm<Delta>
where
    Delta: TrDiscriminant + Clone,
{
    pub a: Integer,
    pub b: Integer,
    D: PhantomData<Delta>,
}

impl<T: TrDiscriminant + Clone> QuadForm<T> {
    pub fn new(a: impl Into<Integer>, b: impl Into<Integer>) -> Self {
        Self {
            a: a.into(),
            b: b.into(),
            D: PhantomData::default(),
        }
    }

    #[inline]
    pub fn get_c(&self) -> Integer {
        let mut val = self.b.clone().square();
        val -= T::Delta_p();
        val /= 4;
        val /= &self.a;
        val
    }

    // Check if $$\gcd(a, b, c) = 1$$.
    #[inline]
    pub fn is_primitive(&self, gcd_abc: Option<&mut Integer>) -> bool {
        let c = self.get_c();
        let mut gcd = self.a.clone().gcd(&self.b);
        gcd = gcd.clone().gcd(&c);
        if let Some(out) = gcd_abc {
            *out = gcd.clone();
        }
        gcd == 1
    }

    #[inline]
    pub fn to_primitive(&self) -> Self {
        let mut gcd = Integer::from(1);
        let _ = self.is_primitive(Some(&mut gcd));
        let a = self.a.clone() / &gcd;
        let b = self.b.clone() / &gcd;
        Self::new(a, b)
    }

    #[inline]
    pub fn is_posdef(&self) -> bool {
        let zero = &Integer::ZERO;
        let Delta = T::Delta_p();
        let a = &self.a;
        return Delta < zero && a > zero;
    }

    // Check if the given positive definite form is reduced.
    #[inline]
    pub fn is_reduced(&self) -> bool {
        let a = &self.a;
        let b = &self.b;
        let _c = self.get_c();
        let c = &_c;

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

    #[inline]
    pub fn identity(&self) -> Self {
        Self::new(1, 1)
    }

    // [Cohen1993, Algorithm 5.4.2]
    // Given a positive definite quadratic form $$f$$, this algorithm outputs
    // the unique reduced form equivalent to $$f$$.
    pub fn reduce(&self) -> Self {
        let (mut a, mut b, mut c) = (self.a.clone(), self.b.clone(), self.get_c());

        loop {
            // Step 1. Initialize.
            let cond = {
                let neg_a = Integer::from(-&a);
                &neg_a < &b && &b <= &a
            };
            if cond {
                // Step 3.
                if &a > &c {
                    (a, b, c) = (c, -b, a);
                    /* goto Step 2. */
                } else {
                    if &a == &c && &b < &Integer::ZERO {
                        b = -b;
                    }
                    return Self::new(a, b);
                }
            }

            // Step 2. Euclidean step.
            let double_a = Integer::from(&a * &Integer::from(2));
            let (mut q, mut r) = b.clone().div_rem_euc(double_a.clone());
            if &r > &a {
                r -= &double_a;
                q += 1;
            }
            c -= (Integer::from(&b + &r) * &q) / 2;
            b = r;
        }
    }

    // [Cohen1993, Algorithm 5.4.7] (not NUCOMP)
    // NUCOMP is [Cohen1993, Algorithm 5.4.9]
    pub fn mul_naive(&self, other: &Self) -> Self {
        let (mut a1, mut b1, mut c1) = (self.a.clone(), self.b.clone(), self.get_c());
        let (mut a2, mut b2, mut c2) = (other.a.clone(), other.b.clone(), other.get_c());

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
        }

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
        // let c3 = Integer::from(&c2 * &d1) + Integer::from(&b2 + &v2r) * &r;
        // let c3 = Integer::from(&c3 / &v1);

        let f3 = Self::new(a3, b3);
        f3.reduce()
    }

    /// TODO: implement NUCOMP
    pub fn mul(&self, other: &Self) -> Self {
        self.mul_naive(other)
    }

    /// TODO: implement NUDUPL
    pub fn square(&self) -> Self {
        self.mul_naive(self)
    }

    /// Just negate B.
    #[inline]
    pub fn inv(&self) -> Self {
        Self::new(self.a.clone(), -self.b.clone())
    }

    pub fn exp(&self, k: &Integer) -> Self {
        let mut base: Self = self.clone();
        let mut res = self.identity();
        let mut expo = k.clone();

        if expo.is_negative() {
            base = self.inv();
            expo = -expo;
        }
        while expo.is_positive() {
            if expo.get_bit(0) {
                // if the least bit is 1.
                res = base.mul(&res);
            }
            base = base.square();
            expo >>= 1;
        }
        res
    }
}

pub struct PartialEuclideanResult {}

#[allow(unused)]
pub fn partial_euclidean(a: &Integer, b: &Integer, L: &Integer) -> PartialEuclideanResult {
    let v = Integer::from(0);
    let d = a.clone();
    let v2 = Integer::from(1);
    let v3 = b.clone();
    let z = Integer::from(0);

    todo!()
}
