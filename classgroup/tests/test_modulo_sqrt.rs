use classgroup::{generator_utils::sqrt_modp, rug_seeded_rng};
use rug::Integer;

#[test]
fn test_mod_sqrt() {
    let mut rng = rug_seeded_rng();
    let mut get_x = || Integer::from(1000).random_below(&mut rng);
    let mut p = Integer::from(2);
    while p < 1000_0000 {
        let mut n = 0;
        while n < 5 {
            let x = get_x();
            if x.legendre(&p) == -1 {
                continue;
            }
            n += 1;
            let y = sqrt_modp(&x, &p).unwrap();
            let x = x.modulo(&p);
            let yy = y.square().modulo(&p);
            assert_eq!(x, yy);
        }
        // println!("p = {p}");
        p = p.next_prime();
    }
}
