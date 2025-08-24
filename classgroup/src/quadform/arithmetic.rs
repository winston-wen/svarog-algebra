use core::fmt;
use std::marker::PhantomData;

use super::*;
use anyhow::{ ensure, Ok };
use rug::Integer;
use serde::{ Deserialize, Serialize };

#[derive(Serialize, Deserialize, Clone, Default, PartialEq, Eq)]
pub struct QuadForm<Delta> where Delta: TrDiscriminant + Clone {
    pub a: Integer,
    pub b: Integer,
    D: PhantomData<Delta>,
}

impl<Delta> fmt::Debug for QuadForm<Delta> where Delta: TrDiscriminant + Clone + 'static {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let c = self.get_c();
        write!(f, "QuadForm({}, {}, {})", &self.a, &self.b, c)
    }
}

impl<T: TrDiscriminant + Clone + 'static> QuadForm<T> {
    pub fn new(a: impl Into<Integer>, b: impl Into<Integer>) -> anyhow::Result<Self> {
        let a: Integer = a.into();
        let b: Integer = b.into();
        let lhs = b.clone().square() - T::Delta_p();
        let rhs = a.clone() * 4;
        let rem = lhs.modulo(&rhs);
        ensure!(rem == 0, "QuadForm::new(...) math broken");

        let res = Self {
            a,
            b,
            D: PhantomData::default(),
        };
        Ok(res)
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
        Self::new(a, b).unwrap()
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
                    return Self::new(a, b).unwrap();
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

        let f3 = Self::new(a3, b3).unwrap();
        f3.reduce()
    }

    /// TODO: implement NUCOMP
    pub fn mul(&self, other: &Self) -> Self {
        self.mul_naive(other)
    }

    pub fn square(&self) -> Self {
        let a = self.a.clone();
        let b = self.b.clone();
        let c = self.get_c();
        let (d1, u, _) = b.clone().extended_gcd(a.clone(), Integer::new());
        let /*mut*/ A = a / &d1;
        let /*mut*/ B = b.clone() / &d1;
        let mut C = (-u * &c).modulo(&A);
        let C1 = A.clone() - &C;
        if C1 < C {
            C = -C1;
        }
        let obj = Self::partial_euclidean(&A, &C);
        let d = obj.d;
        let (mut v, /*mut*/ v2, v3) = (obj.v, obj.v2, obj.v3);
        if !obj.looped {
            let a2 = d.clone().square();
            let c2 = v3.clone().square();
            let b2 = b + (d.clone() + &v3).square() - &a2 - &c2;
            // let g = (c.clone() + &B * &v3) / &d;
            // let c2 = c2 + &g * &d1;
            let f = Self::new(a2, b2).unwrap().reduce();
            return f;
        } else {
            let e = (c.clone() * &v + &B * &d) / &A;
            let g = (e.clone() * &v2 - &B) / &v;
            let mut b2 = e.clone() * &v2 + &v * &g;
            if d1 > 1 {
                b2 = b2 * &d1;
                v = v * &d1;
                // v2 = v2 * &d1;
            }
            let a2 = d.clone().square();
            let c2 = v3.clone().square();
            let b2 = b2 + (d.clone() + &v3).square() - &a2 - &c2;
            let a2 = a2 + &e * &v;
            // let c2 = c2 + &g * &v2;
            let f = Self::new(a2, b2).unwrap().reduce();
            return f;
        }
    }

    /// Just negate B.
    #[inline]
    pub fn inv(&self) -> Self {
        Self::new(self.a.clone(), -self.b.clone()).unwrap()
    }

    pub fn exp(&self, k: &Integer) -> Self {
        let mut base: Self = self.clone();
        let mut res = T::identity().clone();
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

    #[allow(unused)]
    pub fn partial_euclidean(a: &Integer, b: &Integer) -> PartialEuclideanResult {
        let mut d = a.clone();
        let mut v = Integer::from(0);
        let mut v2 = Integer::from(1);
        let mut v3 = b.clone();
        let mut loop_is_odd = false;
        let mut looped = false;

        loop {
            let v3_abs = v3.clone().abs();
            if &v3_abs <= T::L() {
                if loop_is_odd {
                    v2 = -v2;
                    v3 = -v3;
                }
                let res = PartialEuclideanResult {
                    d: d.clone(),
                    v: v.clone(),
                    v2: v2.clone(),
                    v3: v3.clone(),
                    looped,
                };
                return res;
            }
            let (q, t3) = d.clone().div_rem_euc(v3.clone());
            let t2 = Integer::from(&v - &q * &v2);
            v = v2.clone();
            d = v3.clone();
            v2 = t2;
            v3 = t3;
            loop_is_odd = !loop_is_odd;
            looped = true;
        }
    }
}

#[derive(Serialize, Deserialize, Clone, Default)]
pub struct PartialEuclideanResult {
    pub d: Integer,
    pub v: Integer,
    pub v2: Integer,
    pub v3: Integer,
    pub looped: bool,
}
