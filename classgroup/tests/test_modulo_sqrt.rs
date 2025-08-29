use classgroup::{modulo_sqrt::mod_sqrt, rug_seeded_rng};
use rug::Integer;

#[test]
fn test_mod_sqrt() {
    let mut rng = rug_seeded_rng();
    let mut get_x = || Integer::from(1000).random_below(&mut rng);
    let p = Integer::from(2);
    while p < 1000 {
        for _ in 0..5 {
            let x = get_x();
            let y = mod_sqrt(&x, &p);
            let x = x.modulo(&p);
            let yy = y.square().modulo(&p);
            assert_eq!(x, yy);
        }
    }
}
