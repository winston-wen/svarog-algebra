#![allow(nonstandard_style)]

use std::io::Write;
use std::{fs::OpenOptions, path::PathBuf, str::FromStr, time::Duration};

use cl_playground::MmapVecU64;
use clap::{Arg, ArgAction, Command, value_parser};
use classgroup::{generator_utils::sqrt_mod4p, quadform::QuadForm};
use indicatif::{ProgressBar, ProgressStyle};
use rug::{Integer, ops::Pow};

// mod cached;
// use cached::*;

fn main() {
    // p mod 4 == 1
    let p = Integer::from_str(
        "115792089237316195423570985008687907852837564279074904382605163141518161494337",
    )
    .unwrap();

    let q: Integer = Integer::from(1) << (1827 - 256);
    let mut q = q.next_prime();
    let mut cond = false;
    while !cond {
        q = q.next_prime();

        // By [CL15, Appendix B.3] and [Kap78, p. 598], the following constraint
        // aims at minimizing the 2-Sylow subgroup of CL(-pq).
        cond = p.kronecker(&q) == -1 && q.kronecker(&p) == -1;

        // The following constraint ensures that $$-pq = 1 \bmod 4$$, which
        // further ensures that $$\Delta_K = b^2 - 4ac$$ is a valid discriminant.
        cond = cond && q.clone() % 4 == 3;
    }

    let Delta_K = p.clone() * &q;
    let Delta_K = -Delta_K;

    println!("====================");
    println!("p = {}", p.to_string_radix(16));
    println!("q = {}", q.to_string_radix(16));
    println!("log2(Delta_K) = {}", Delta_K.significant_bits());

    let mut ra = Integer::from(2).pow(512).next_prime();
    while Delta_K.kronecker(&ra) != 1 {
        ra = ra.next_prime();
    }
    let rb = sqrt_mod4p(&Delta_K, ra.clone()).unwrap();
    let g = QuadForm::new(&ra, &rb, &Delta_K).unwrap().square();

    println!("====================");
    println!("This program will check if $$g^p=0$$ for p,");
    println!("\tfrom p{beg} to p{end}.");

    let primes = {
        let home = std::env::var("HOME").unwrap_or_else(|_| ".".to_string());
        let path = format!("{home}/primes/prime.dat");
        let primes = MmapVecU64::from_file(&path).unwrap();
        primes
    };

    let g2t = {
        let nbits = primes[end as usize].significant_bits() as usize;
        let mut res = vec![g.clone(); nbits];
        for t in 1..nbits {
            res[t] = res[t - 1].square();
        }
        res
    };

    let g_exp = |p: &Integer| -> QuadForm {
        let mut res = g.new_identity();
        for t in 0..p.significant_bits() {
            if p.get_bit(t as u32) {
                res = res.mul(&g2t[t as usize]);
            }
        }
        res
    };

    println!("====================");
    println!("Checking if ⟨g⟩ is safe.");

    let progbar = ProgressBar::new((end - beg + 1) as u64);
    let style = ProgressStyle::with_template("{percent:>3.1}% |{bar:50}| ({per_sec}, {eta})")
        .unwrap()
        .progress_chars("#o-");
    progbar.set_style(style.clone());
    progbar.enable_steady_tick(Duration::from_millis(500));

    for i in beg..=end {
        let p = &primes[i as usize];
        let gp = g_exp(p);
        let gp2 = g.exp(p);
        assert_eq!(gp, gp2);
        if gp.is_identity() {
            progbar.abandon();
            println!("⟨g⟩ has small prime subgroup of order: {}", &p);
            writeln!(file, "p{i} fucked up").unwrap();
            file.sync_all().unwrap();
            return;
        }

        // write to file
        '_write_file: {
            // use std::io::{Seek, SeekFrom};
            // file.seek(SeekFrom::Start(0)).unwrap();
            // file.set_len(0).unwrap();
            writeln!(file, "p{i}").unwrap();
            file.sync_all().unwrap();
        }

        progbar.inc(1);
    }
    progbar.finish();
    println!("Lucky! ⟨g⟩ has no small prime subgroup.")
}
