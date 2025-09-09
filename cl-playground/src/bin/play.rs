#![allow(nonstandard_style)]

use std::time::Duration;

use cl_playground::{MmapVecU64, g_exp};
use clap::{Arg, ArgAction, Command};
use indicatif::{ProgressBar, ProgressStyle};

// mod cached;
// use cached::*;

fn main() {
    let matches = Command::new("playground")
        .arg(
            Arg::new("task")
                .required(false)
                .default_value("1/1")
                .action(ArgAction::Set),
        )
        .get_matches();

    let task = matches.get_one::<String>("task").unwrap().to_owned();
    let task: Vec<&str> = task.split('/').collect();
    assert!(task.len() == 2);
    let num: usize = task[0].parse().expect("an integer");
    let den: usize = task[1].parse().expect("an integer");
    assert!(num >= 1 && den >= 1 && num <= den);

    let primes = {
        let home = std::env::var("HOME").unwrap_or_else(|_| ".".to_string());
        let path = format!("{home}/primes/all_primes.dat");
        let primes = MmapVecU64::from_file(&path).unwrap();
        primes
    };
    let stride = primes.len() / den;
    let rem = primes.len() % den;
    let beg = if num == 1 {
        1
    } else {
        (num - 1) * stride + rem
    };
    let end = num * stride + rem;

    println!("===== Class Group Parameters =====");
    println!("p = {}", cl_playground::P.to_string_radix(16));
    println!("q = {}", cl_playground::Q.to_string_radix(16));
    println!(
        "log2(Delta_K) = {}",
        cl_playground::Delta_K.significant_bits()
    );
    println!();

    println!("===== Check if ⟨g⟩ is safe =====");
    println!("Check from p{beg} (inclusive) to p{end} (exclusive).");

    let progbar = ProgressBar::new((end - beg) as u64);
    let style = ProgressStyle::with_template("{percent:>3.1}% |{bar:50}| ({per_sec}, {eta})")
        .unwrap()
        .progress_chars("#o-");
    progbar.set_style(style.clone());
    progbar.enable_steady_tick(Duration::from_millis(500));

    for i in beg..end {
        let p = &primes[i];
        let gp = g_exp(*p);
        if gp.is_identity() {
            progbar.abandon();
            println!("⟨g⟩ has small prime subgroup of order: {}", &p);
            return;
        }
        progbar.inc(1);
    }
    progbar.finish();
    println!("Lucky! ⟨g⟩ has no small prime subgroup.")
}
