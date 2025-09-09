#![allow(nonstandard_style)]

mod math {
    use classgroup::generator_utils::sqrt_mod4p;
    use classgroup::naf::NafInteger;
    use classgroup::quadform::QuadForm;
    use rug::Integer;
    use rug::ops::Pow;
    use std::str::FromStr;
    use std::sync::LazyLock;

    pub static P: LazyLock<Integer> = LazyLock::new(|| {
        // p mod 4 == 1
        Integer::from_str(
            "115792089237316195423570985008687907852837564279074904382605163141518161494337",
        )
        .unwrap()
    });

    pub static Q: LazyLock<Integer> = LazyLock::new(|| {
        let mut q: Integer = Integer::from(1) << (1827 - 256);
        q = q.next_prime();
        let mut cond = false;
        while !cond {
            q = q.next_prime();

            // By [CL15, Appendix B.3] and [Kap78, p. 598], the following constraint
            // aims at minimizing the 2-Sylow subgroup of CL(-pq).
            cond = P.kronecker(&q) == -1 && q.kronecker(&P) == -1;

            // The following constraint ensures that $$-pq = 1 \bmod 4$$, which
            // further ensures that $$\Delta_K = b^2 - 4ac$$ is a valid discriminant.
            cond = cond && q.clone() % 4 == 3;
        }
        q
    });

    pub static Delta_K: LazyLock<Integer> = LazyLock::new(|| {
        let d = P.clone() * Q.clone();
        -d
    });

    pub static G: LazyLock<QuadForm> = LazyLock::new(|| {
        let mut ra = Integer::from(2).pow(512).next_prime();
        while Delta_K.kronecker(&ra) != 1 {
            ra = ra.next_prime();
        }
        let rb = sqrt_mod4p(&Delta_K as &Integer, ra.clone()).unwrap();
        let g = QuadForm::new(&ra, &rb, &Delta_K as &Integer)
            .unwrap()
            .square();
        g
    });

    pub const nbits: usize = 2048;

    pub static TableG: LazyLock<Vec<QuadForm>> = LazyLock::new(|| {
        let mut table = vec![G.clone(); nbits];
        for t in 1..nbits {
            table[t] = table[t - 1].square();
        }
        table
    });

    pub fn g_exp(x: impl Into<Integer>) -> QuadForm {
        let x: Integer = x.into();
        assert!((x.significant_bits() as usize) < nbits);

        let x = NafInteger::from_integer(&x);
        let mut h = G.new_identity();

        for (t, d) in x.iter().enumerate() {
            match d {
                classgroup::naf::NafDigit::Zero => {}
                classgroup::naf::NafDigit::One => h = h.mul(&TableG[t]),
                classgroup::naf::NafDigit::NegOne => h = h.mul(&TableG[t].inv()),
            }
        }
        h
    }
}
pub use math::*;

#[cfg(test)]
mod tests {
    use classgroup::{cl_elgamal::cl_params, rug_seeded_rng};
    use rug::{Integer, ops::Pow};

    use crate::g_exp;

    #[test]
    fn test_g_exp() {
        let g = cl_params::generator_Delta_K();
        let mut rng = rug_seeded_rng();
        let x = Integer::from(2).pow(1024).random_below(&mut rng);

        let h1 = g.exp(&x);
        let h2 = g_exp(x);
        assert_eq!(h1, h2);
    }
}

mod mmap_vec {
    use anyhow::bail;
    use memmap2::{Mmap, MmapOptions};
    use std::fs::File;
    use std::io::Write;
    use std::ops::Index;
    use std::sync::Arc;

    pub struct MmapVecU64 {
        _mmap: Arc<Mmap>, // 保持 mmap 的生命周期
        data: &'static [u64],
    }

    impl MmapVecU64 {
        pub fn from_file(path: &str) -> anyhow::Result<Self> {
            let file = File::open(path)?;
            let mmap = unsafe { MmapOptions::new().map(&file)? };

            if mmap.len() % std::mem::size_of::<u64>() != 0 {
                bail!("File size is not multiple of sizeof(u64)");
            }

            let len = mmap.len() / std::mem::size_of::<u64>();
            let ptr = mmap.as_ptr() as *const u64;
            let data = unsafe { std::slice::from_raw_parts(ptr, len) };

            let mmap = Arc::new(mmap);

            Ok(MmapVecU64 {
                _mmap: mmap,
                data: unsafe { std::mem::transmute(data) },
            })
        }

        pub fn as_slice(&self) -> &[u64] {
            self.data
        }

        pub fn len(&self) -> usize {
            self.data.len()
        }

        pub fn save_one(val: u64, file: &mut File) -> anyhow::Result<()> {
            let bytes = val.to_le_bytes();
            file.write_all(&bytes)?;
            Ok(())
        }

        pub fn save_many(data: &[u64], file: &mut File) -> anyhow::Result<()> {
            let bytes = unsafe {
                std::slice::from_raw_parts(
                    data.as_ptr() as *const u8,
                    data.len() * std::mem::size_of::<u64>(),
                )
            };
            file.write_all(bytes)?;
            return Ok(());
        }
    }

    impl Index<usize> for MmapVecU64 {
        type Output = u64;

        fn index(&self, index: usize) -> &Self::Output {
            &self.as_slice()[index]
        }
    }
}
pub use mmap_vec::*;
