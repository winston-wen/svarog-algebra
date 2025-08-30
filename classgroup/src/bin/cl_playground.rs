#![allow(nonstandard_style)]

use std::time::Duration;

use classgroup::{cl_elgamal::delta1827, generator_utils::sqrt_mod4p, quadform::QuadForm};
use indicatif::{ProgressBar, ProgressStyle};
use rug::{Integer, ops::Pow};

fn main() {
    let p = delta1827::p(); // p mod 4 == 1
    // let q = delta1827::q().clone(); // also OK.
    let mut q = p.clone().square().square().next_prime();
    let mut cond = false;
    while !cond {
        q = q.next_prime();

        // By [CL15, Appendix B.3] and [Kap78, p. 598], the following constraint
        // aims at minimizing the 2-Sylow subgroup of CL(-pq).
        cond = p.kronecker(&q) == -1 && q.kronecker(p) == -1;

        // The following constraint ensures that $$-pq = 1 \bmod 4$$, which
        // further ensures that $$\Delta_K = b^2 - 4ac$$ is a valid discriminant.
        cond = cond && q.clone() % 4 == 3;
    }
    println!("q = {}", q.to_string_radix(16));
    let Delta_K = p * q;
    let Delta_K = -Delta_K;

    let mut ra = Integer::from(2).pow(512).next_prime();
    while Delta_K.kronecker(&ra) != 1 {
        ra = ra.next_prime();
    }

    let rb = sqrt_mod4p(&Delta_K, ra.clone()).unwrap();
    println!("r.a = {}", ra.to_string_radix(16));
    println!("r.b = {}", rb.to_string_radix(16));

    let g = QuadForm::new(ra, rb, Delta_K).unwrap().square();
    println!("g.a = {}", g.a.to_string_radix(16));
    println!("g.b = {}", g.b.to_string_radix(16));

    println!("====================");
    println!("Checking if ⟨g⟩ is safe.");

    let beg = 1;
    let end = 10_0000;
    let progbar = ProgressBar::new(end - beg + 1);
    progbar.set_style(
        ProgressStyle::with_template("{percent:>3.1}% |{bar:50}| ({eta})")
            .unwrap()
            .progress_chars("#o-"),
    );
    progbar.enable_steady_tick(Duration::from_millis(500));
    progbar.set_prefix("Test g^p");

    let mut p = Integer::from(2);
    let id = g.new_identity();
    for _ in beg..=end {
        let gp = g.exp(p.clone());
        if gp == id {
            progbar.abandon();
            println!("⟨g⟩ has small prime subgroup of order: {}", &p);
            return;
        }
        p = p.next_prime();
        progbar.inc(1);
    }
    progbar.finish();
    println!("Lucky! ⟨g⟩ has no small prime subgroup.")
}
