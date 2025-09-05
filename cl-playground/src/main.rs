#![allow(nonstandard_style)]

use std::{str::FromStr, time::Duration};

use clap::{Arg, ArgAction, Command, value_parser};
use classgroup::{generator_utils::sqrt_mod4p, quadform::QuadForm};
use indicatif::{ProgressBar, ProgressStyle};
use rug::{Integer, ops::Pow};

fn main() {
    let matches = Command::new("cl-playground")
        .arg(
            Arg::new("from")
                .short('f')
                .required(false)
                .default_value("1")
                .value_parser(value_parser!(i32))
                .action(ArgAction::Set),
        )
        .arg(
            Arg::new("to")
                .short('t')
                .required(false)
                .default_value("200000")
                .value_parser(value_parser!(i32))
                .action(ArgAction::Set),
        )
        .get_matches();
    let beg: i32 = matches.get_one::<i32>("from").unwrap().to_owned();
    let end: i32 = matches.get_one::<i32>("to").unwrap().to_owned();
    assert!(beg >= 1, "command arg from >= 1");
    assert!(end >= beg, "command arg to >= from");
    let (beg, end) = (beg, end);

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

    let style = ProgressStyle::with_template("{percent:>3.1}% |{bar:50}| ({eta})")
        .unwrap()
        .progress_chars("#o-");

    println!("====================");
    println!("This program will check if $$g^p=0$$ for p,");
    println!("\tfrom prime No.{beg} to prime No.{end}.");
    println!("First, we find prime No.{beg}.");

    let progbar = ProgressBar::new(beg as u64);
    progbar.set_style(style.clone());
    progbar.enable_steady_tick(Duration::from_millis(500));
    let mut p = Integer::from(2);
    progbar.inc(1);
    for _ in 1..beg {
        p = p.next_prime();
        progbar.inc(1);
    }
    progbar.finish();
    println!("Found No.{beg} prime = {}", &p);

    println!("====================");
    println!("Checking if ⟨g⟩ is safe.");

    let progbar = ProgressBar::new((end - beg + 1) as u64);
    progbar.set_style(style.clone());
    progbar.enable_steady_tick(Duration::from_millis(500));

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
