use std::fs::create_dir_all;

use cl_playground::MmapVecU64;
use clap::{Arg, ArgAction, Command, value_parser};
use rug::{Integer, integer::IsPrime};

fn main() {
    let matches = Command::new("primes")
        .arg(
            Arg::new("from")
                .required(false)
                .default_value("0")
                .value_parser(value_parser!(u64))
                .action(ArgAction::Set),
        )
        .get_matches();
    let from = matches.get_one::<u64>("from").unwrap().to_owned();
    let (beg, end) = (from << 32, (from + 1) << 32);

    let mut file = {
        use std::fs::OpenOptions;
        use std::path::PathBuf;

        let home = std::env::var("HOME").unwrap_or_else(|_| ".".to_string());
        let file_path = PathBuf::from(home).join(format!("primes"));
        create_dir_all(&file_path).unwrap();
        let from = from + 1;
        let file_path = file_path.join(format!("primes.{from}.dat"));
        let file = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(&file_path)
            .unwrap();
        file
    };

    let mut p = {
        let mut p = Integer::from(beg);
        if p.is_probably_prime(40) == IsPrime::No {
            p = p.next_prime();
        }
        p.to_u64().unwrap()
    };
    MmapVecU64::save_one(p, &mut file).unwrap();

    while p <= end {
        let p2 = Integer::from(p).next_prime().to_u64().unwrap();
        MmapVecU64::save_one(p2, &mut file).unwrap();
        p = p2;
        println!("p={p}");
    }
}
