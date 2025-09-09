use core::fmt;

use anyhow::{Context, Ok, ensure};
use rug::Integer;
use serde::{Deserialize, Serialize};

use crate::naf::{NafDigit, NafInteger};

#[derive(Serialize, Deserialize, Clone, Default, PartialEq, Eq)]
pub struct QuadForm {
    pub a: Integer,
    pub b: Integer,
    pub Delta: Integer,
    pub L: Integer,
}

impl fmt::Debug for QuadForm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let c = self.get_c();
        write!(f, "QuadForm({}, {}, {})", &self.a, &self.b, c)
    }
}

impl QuadForm {
    pub fn new(
        a: impl Into<Integer>,
        b: impl Into<Integer>,
        Delta: impl Into<Integer>,
    ) -> anyhow::Result<Self> {
        let a: Integer = a.into();
        let b: Integer = b.into();
        let Delta: Integer = Delta.into();
        let is_posdef = Delta.is_negative() && a.is_positive();
        ensure!(
            is_posdef,
            "QuadForm::new(...) only accepts a posdef binary quadform."
        );

        let lhs = b.clone().square() - &Delta;
        let rhs = 4 * a.clone();
        let rem = lhs.modulo(&rhs);
        ensure!(rem == 0, "QuadForm::new(...) failed to find integer c");

        let L = (Delta.clone().abs() / Integer::from(4)).sqrt().sqrt();

        let res = Self { a, b, Delta, L };
        Ok(res)
    }

    #[inline]
    pub fn new_identity(&self) -> Self {
        // Here we trust that `self.Delta` and `self.L` are correct.
        return Self {
            a: (1).into(),
            b: (1).into(),
            Delta: self.Delta.clone(),
            L: self.L.clone(),
        };
    }

    pub fn new_alike(&self, a: impl Into<Integer>, b: impl Into<Integer>) -> anyhow::Result<Self> {
        let a = a.into();
        let b = b.into();
        let Delta = self.Delta.clone();
        let is_posdef = Delta.is_negative() && a.is_positive();
        ensure!(
            is_posdef,
            "QuadForm::new_alike(...) only accepts a posdef binary quadform."
        );

        let lhs = b.clone().square() - &Delta;
        let rhs = 4 * a.clone();
        let rem = lhs.modulo(&rhs);
        ensure!(
            rem == 0,
            "QuadForm::new_alike(...) failed to find integer c"
        );

        // Here we trust that `self.L` is correct.
        let L = self.L.clone();

        let res = Self { a, b, Delta, L };
        Ok(res)
    }

    #[inline]
    pub fn get_c(&self) -> Integer {
        return (self.b.clone().square() - &self.Delta) / 4 / &self.a;
    }

    // Check if $$\gcd(a, b, c) = 1$$.
    #[inline]
    pub fn is_identity(&self) -> bool {
        return self.a == 1 && self.b == 1;
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
        Self::new(a, b, &self.Delta).unwrap()
    }

    #[inline]
    pub fn is_posdef(&self) -> bool {
        return self.Delta.is_negative() && self.a.is_positive();
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
                    return Self::new(a, b, &self.Delta).unwrap();
                }
            }

            // Step 2. Euclidean step.
            let double_a: Integer = a.clone() * 2;
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
    #[allow(dead_code)]
    pub(crate) fn mul_naive(&self, other: &Self) -> Self {
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

        let f3 = self.new_alike(a3, b3).unwrap();
        f3.reduce()
    }

    /// [Cohen1993, Algorithm 5.4.8] NUDUPL
    /// Reimplement `def _compose(...)` of
    /// https://github.com/GiacomoPope/ClassGroups/blob/main/classgroup.py
    pub fn mul(&self, other: &Self) -> Self {
        assert_eq!(
            self.Delta, other.Delta,
            "QuadForm::mul(...) refuses to multiply quadforms with different discriminant."
        );
        let (mut a1, mut b1, mut c1) = (self.a.clone(), self.b.clone(), self.get_c());
        let (mut a2, mut b2, mut c2) = (other.a.clone(), other.b.clone(), other.get_c());

        // Step 1. Initialize.
        if a1 < a2 {
            (a1, b1, c1, a2, b2, c2) = (a2, b2, c2, a1, b1, c1);
        }
        let mut s: Integer = (b1.clone() + &b2) / 2;
        let n = b2.clone() - &s;

        // Step 2. First Euclidean step.
        let (mut d, u, v) = a2.clone().extended_gcd(a1.clone(), Integer::new());
        let (mut A, /*mut*/ d1): (Integer, Integer);
        if s.clone() % &d == 0 {
            A = -u.clone() * &n;
            d1 = d.clone();
            if d != 1 {
                a1 /= &d1;
                a2 /= &d1;
                s /= &d1;
            }
        } else {
            // Step 3. Second Euclidean step.
            let (_d1, u1, _v1) = s.clone().extended_gcd(d.clone(), Integer::new());
            d1 = _d1;
            if d1 > 1 {
                a1 /= &d1;
                a2 /= &d1;
                s /= &d1;
                d /= &d1;
            }

            // Step 4. Initialization of reduction.
            let (c1, c2) = (c1.clone() % &d, c2.clone() % &d);
            let l = (-u1 * (u.clone() * &c1 + &v * &c2)) % &d;
            A = -u * (n.clone() / &d) + l * (a1.clone() / &d);
        }

        // Step 5. Partial reduction.
        A = A % &a1;
        let A1 = a1.clone() - &A;
        if A1 < A {
            A = -A1;
        }
        let obj = Self::partial_euclidean(&a1, &A, &self.L);
        let (d, mut v, v2, v3, looped) = (obj.d, obj.v, obj.v2, obj.v3, obj.looped);

        // Step 6. Special case.
        if !looped {
            let Q1 = a2.clone() * &v3;
            let a3 = d.clone() * a2;
            let b3 = 2 * Q1 + &b2;
            return self.new_alike(a3, b3).unwrap().reduce();
        }

        // Step 7. Final computations
        let b = (a2 * &d + &n * &v) / &a1;
        let Q1 = b.clone() * &v3;
        let Q2 = Q1.clone() + &n;
        let e = (s.clone() * &d + &c2 * &v) / &a1;
        let Q3 = e.clone() * v2;
        let Q4 = Q3.clone() - s;
        if d1 > 1 {
            v = d1.clone() * v;
        }
        let a3 = d * b + e * v;
        let b3 = Q1 + Q2 + d1 * (Q3 + Q4);
        return self.new_alike(a3, b3).unwrap().reduce();
    }

    /// [Cohen1993, Algorithm 5.4.8] NUDUPL
    /// Reimplement `def _square(...)` of
    /// https://github.com/GiacomoPope/ClassGroups/blob/main/classgroup.py
    pub fn square(&self) -> Self {
        let a = self.a.clone();
        let b = self.b.clone();
        let c = self.get_c();
        let (d1, u, _) = b.clone().extended_gcd(a.clone(), Integer::new());

        let /*mut*/ A = a / &d1;
        let /*mut*/ B = b.clone() / &d1;
        let mut C = (-c.clone() * &u).modulo(&A);
        let C1 = A.clone() - &C;
        if C1 < C {
            C = -C1;
        }

        let obj = Self::partial_euclidean(&A, &C, &self.L);
        let d = obj.d;
        let (mut v, /*mut*/ v2, v3) = (obj.v, obj.v2, obj.v3);
        if !obj.looped {
            let a2 = d.clone().square();
            let b2 = b + 2 * d * v3;
            return self.new_alike(a2, b2).unwrap().reduce();
        }

        let e = (c * &v + &B * &d) / &A;
        let g = (e.clone() * &v2 - &B) / &v;
        let mut b2 = e.clone() * &v2 + &v * &g;
        if d1 > 1 {
            b2 = b2 * &d1;
            v = v * &d1;
        }
        let a2 = d.clone().square() + &e * &v;
        let b2 = b2 + 2 * d * v3;
        return self.new_alike(a2, b2).unwrap().reduce();
    }

    /// Just negate B.
    #[inline]
    pub fn inv(&self) -> Self {
        Self::new(self.a.clone(), -self.b.clone(), &self.Delta).unwrap()
    }

    #[allow(dead_code)]
    pub(crate) fn exp_naive(&self, k: impl Into<Integer>) -> Self {
        let mut base: Self = self.clone();
        let mut res = self.new_identity();
        let mut expo = k.into();

        if expo.is_negative() {
            base = self.inv();
            expo = -expo;
        }
        while expo.is_positive() {
            if expo.is_odd() {
                // if the least bit is 1.
                res = base.mul(&res);
            }
            base = base.square();
            expo >>= 1;
        }
        res
    }

    pub fn exp(&self, k: impl Into<Integer>) -> Self {
        let mut base: Self = self.clone();
        let mut res = self.new_identity();

        let mut expo = k.into();
        if expo.is_negative() {
            base = self.inv();
            expo = -expo;
        }
        let base = base;

        let expo = NafInteger::from_integer(expo);
        expo.validate().unwrap();

        for naf_digit in expo.iter().rev() {
            res = res.square();

            match naf_digit {
                NafDigit::One => {
                    res = res.mul(&base);
                }
                NafDigit::NegOne => {
                    res = res.mul(&base.inv());
                }
                NafDigit::Zero => {}
            }
        }

        return res;
    }

    #[allow(unused)]
    /// Reimplement `def part_eucl(...)` of
    /// https://github.com/GiacomoPope/ClassGroups/blob/main/classgroup_helper.py
    pub fn partial_euclidean(
        a: impl Into<Integer>,
        b: impl Into<Integer>,
        L: impl Into<Integer>,
    ) -> PartialEuclideanResult {
        let mut v = Integer::from(0);
        let mut v2 = Integer::from(1);
        let mut v3 = b.into();
        let mut d = a.into();
        let L = L.into();
        let mut loop_is_odd = false;
        let mut looped = false;

        while v3.clone().abs() > L {
            let (mut q, t3) = d.clone().div_rem_euc(v3.clone());
            let t2 = Integer::from(&v - &q * &v2);
            (v, d) = (v2, v3);
            (v2, v3) = (t2, t3);
            loop_is_odd = !loop_is_odd;
            looped = true;
        }
        if loop_is_odd {
            (v2, v3) = (-v2, -v3);
        }

        return PartialEuclideanResult {
            d,
            v,
            v2,
            v3,
            looped,
        };
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        serde_pickle::to_vec(self, Default::default()).unwrap()
    }

    pub fn from_bytes(buf: &[u8]) -> anyhow::Result<Self> {
        let obj: Self = serde_pickle::from_slice(buf, Default::default())
            .with_context(|| "Failed to deserialize a QuadForm")?;
        let obj = Self::new(obj.a, obj.b, obj.Delta)
            .with_context(|| "Deserialized an invalid QuadForm")?;

        Ok(obj)
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
