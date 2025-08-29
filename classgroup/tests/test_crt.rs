use classgroup::{generator_utils::crt, rug_seeded_rng};
use rand::RngCore;
use rug::{Integer, ops::Pow};

#[test]
fn test_crt() {
    let mut rng1 = rug_seeded_rng();
    let mut rng2 = rug_seeded_rng();
    let mut rng3 = rand::rng();
    let mut rng4 = rand::rng();
    let mut get_x = || Integer::from(1000_0000_0000u64).random_below(&mut rng1);
    let mut get_p = || Integer::from(100).random_below(&mut rng2);
    let mut get_e = || rng3.next_u32() % 4 + 1;

    for _i in 1..=100 {
        let gt = get_x();
        let mut w = Integer::from(1);
        let mut xs = Vec::new();
        let mut ws = Vec::new();
        let len = rng4.next_u32() % 4 + 1;
        let mut pi = get_p();
        for _ in 0..len {
            pi = pi.next_prime();
            let ei = get_e();
            let wi = pi.clone().pow(ei);
            let xi = gt.clone() % &wi;

            w *= &wi;
            xs.push(xi);
            ws.push(wi);
        }

        let x = crt(&xs, &ws);
        let gt = gt % w;
        assert_eq!(x, gt);
    }
}
