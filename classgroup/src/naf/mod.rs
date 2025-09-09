use std::ops::{Deref, DerefMut};

use anyhow::bail;
use rug::Integer;
use serde::{Deserialize, Serialize};

#[repr(transparent)]
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct NafInteger(Vec<NafDigit>);

impl Default for NafInteger {
    fn default() -> Self {
        NafInteger(vec![NafDigit::Zero])
    }
}

impl Deref for NafInteger {
    type Target = Vec<NafDigit>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for NafInteger {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[derive(Serialize, Deserialize, Debug, Clone, Copy, PartialEq, Eq)]
pub enum NafDigit {
    Zero,
    One,
    NegOne,
}

impl NafInteger {
    /// Use Prodinger's method to convert a `rug::Integer` to an LSF `NafInteger`.
    pub fn from_integer(x: impl Into<Integer>) -> NafInteger {
        let x: Integer = x.into();
        assert!(x >= 0);
        if x == 0 {
            return NafInteger::default();
        }

        // Main part of Prodinger's method.
        let xh: Integer = x.clone() >> 1;
        let x3: Integer = x + xh.clone();
        let c: Integer = xh.clone() ^ x3.clone();
        let np: Integer = x3 & c.clone();
        let nm: Integer = xh & c;

        // 计算需要的位数
        let max_bits = std::cmp::max(np.significant_bits(), nm.significant_bits()) as usize;
        let total_bits = if max_bits == 0 { 1 } else { max_bits };

        let mut result = Vec::with_capacity(total_bits);

        // 构建 NAF 表示
        for i in 0..total_bits {
            let np_bit = np.get_bit(i as u32);
            let nm_bit = nm.get_bit(i as u32);

            let digit = match (np_bit, nm_bit) {
                (true, false) => NafDigit::One,
                (false, true) => NafDigit::NegOne,
                (false, false) => NafDigit::Zero,
                (true, true) => unreachable!("NAF should not have adjacent non-zero bits"),
            };

            result.push(digit);
        }

        // Remove most significant zeros.
        while result.len() > 1 && result.last() == Some(&NafDigit::Zero) {
            result.pop();
        }

        return NafInteger(result);
    }

    pub fn validate(&self) -> anyhow::Result<()> {
        for i in 0..self.len().saturating_sub(1) {
            if self[i] != NafDigit::Zero && self[i + 1] != NafDigit::Zero {
                bail!("NAF should not have adjacent nonzero digits");
            }
        }
        return Ok(());
    }

    pub fn to_integer(&self) -> Integer {
        let mut result = Integer::new();
        let mut power = Integer::from(1);

        for digit in self.iter() {
            match digit {
                NafDigit::One => result += &power,
                NafDigit::NegOne => result -= &power,
                NafDigit::Zero => {}
            }
            power <<= 1;
        }

        result
    }

    pub fn to_string(&self) -> String {
        let mut repr = String::new();
        for d in self.iter().rev() {
            match d {
                NafDigit::Zero => {
                    repr += "0";
                }
                NafDigit::One => {
                    repr += "p";
                }
                NafDigit::NegOne => {
                    repr += "m";
                }
            }
        }
        return repr;
    }
}
