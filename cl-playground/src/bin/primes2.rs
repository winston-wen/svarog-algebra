use cl_playground::MmapVecU64;

fn main() {
    let primes = {
        let home = std::env::var("HOME").unwrap_or_else(|_| ".".to_string());
        let path = format!("{home}/primes/all_primes.dat");
        let primes = MmapVecU64::from_file(&path).unwrap();
        primes
    };
    println!("primes.len == {}", primes.len());
    println!("primes[114514] == {}", primes[114514]);
    println!("primes[1919810] == {}", primes[1919810]);
    println!("primes[-1] == {}", primes[primes.len() - 1]);
}
