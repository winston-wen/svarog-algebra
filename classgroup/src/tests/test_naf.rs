use crate::{
    cl_elgamal::cl_params,
    naf::{NafDigit, NafInteger},
    rug_seeded_rng,
};
use rug::{Integer, ops::Pow};

#[test]
fn test_naf() {
    let mut rng = rug_seeded_rng();
    let n2048 = Integer::from(2).pow(2048).random_below(&mut rng);
    let naf = NafInteger::from_integer(&n2048);
    naf.validate().unwrap();
    let n = naf.to_integer();
    assert_eq!(n2048, n);

    let mut before = 0;
    for i in 0..n2048.significant_bits() {
        if n2048.get_bit(i) == false {
            before += 1;
        }
    }

    let mut after = 0;
    for i in 0..naf.len() {
        if naf[i] == NafDigit::Zero {
            after += 1;
        }
    }

    println!("before={before}, after={after}");

    assert!(before <= after);
}

#[test]
fn test_exp() {
    let g = cl_params::generator_Delta_K();
    let mut rng = rug_seeded_rng();
    let x = Integer::from(2).pow(1024).random_below(&mut rng);
    let h1 = g.exp(&x);
    let h2 = g.exp_naive(&x);
    assert_eq!(h1, h2);
}

#[test]
fn test_repr() {
    let x = Integer::from(7);
    let repr = NafInteger::from_integer(x).to_string();
    assert_eq!(repr, "p00m");
}
