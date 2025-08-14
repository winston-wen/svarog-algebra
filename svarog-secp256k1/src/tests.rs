use crate::*;

#[test]
fn test_scalar() {
    // test add
    let a = Scalar::new(114514);
    let b = Scalar::new(-1919);
    let c0 = Scalar::new(114514 - 1919);
    let c1 = a.add(&b);
    let c2 = b.add(&a);
    assert_eq!(c1, c0);
    assert_eq!(c1, c2);

    // test neg
    assert_eq!(b.neg(), Scalar::new(1919));

    // test mul
    let c0 = Scalar::new(-114514 * 1919);
    let c1 = a.mul(&b);
    let c2 = b.mul(&a);
    assert_eq!(c1, c0);
    assert_eq!(c1, c2);

    // test inv
    let one = Scalar::new(1);
    let mut rng = rand::rng();
    let a = Scalar::new_rand(&mut rng);
    let b = a.inv_ct();
    let c = a.inv_vt();
    assert_eq!(b, c);
    let must_one = a.mul(&b);
    assert_eq!(must_one, one);

    // test inv0
    let zero = Scalar::new(0);
    let a = zero.inv_ct();
    let b = zero.inv_vt();
    assert_eq!(a, b);
    assert_eq!(a, zero);

    let a = Scalar::new_from_be_bytes([0xFFu8; 32]);
    #[rustfmt::skip]
    let gt = Scalar::new_from_be_bytes([
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
        0x45, 0x51, 0x23, 0x19, 0x50, 0xb7, 0x5f, 0xc4,
        0x40, 0x2d, 0xa1, 0x73, 0x2f, 0xc9, 0xbe, 0xbe,
    ]);
    assert_eq!(a, gt);
}

#[test]
fn test_point() {
    let mut rng = rand::rng();

    // new identity point
    let p = Point::new_gx(&ZERO);
    assert_eq!(p, Point::new_identity());

    // new random point addition
    let x1 = Scalar::new_rand(&mut rng);
    let p1 = Point::new_gx(&x1);
    let x2 = Scalar::new_rand(&mut rng);
    let p2 = Point::new_gx(&x2);
    let p31 = p1.add(&p2);
    let p32 = p2.add(&p1);
    let p33 = p1.add_gx(&x2);
    let p34 = p2.add_gx(&x1);
    let p30 = Point::new_gx(&x1.add(&x2));
    assert_eq!(p31, p30);
    assert_eq!(p32, p30);
    assert_eq!(p33, p30);
    assert_eq!(p34, p30);
    assert_ne!(p30, Point::new_identity());

    // new random point add 0
    let x = Scalar::new_rand(&mut rng);
    let p0 = Point::new_gx(&x);
    let p1 = p0.add_gx(&ZERO);
    let p2 = ID.add_gx(&x);
    let p3 = p0.add(&ID);
    let p4 = ID.add(&p0);
    assert_eq!(p1, p0);
    assert_eq!(p2, p0);
    assert_eq!(p3, p4);
    assert_eq!(p3, p0);
    assert_eq!(p4, p0);
    assert_ne!(p0, Point::new_identity());

    // new random points sum to 0
    let x = Scalar::new_rand(&mut rng);
    let p0 = ID.clone();
    let p1 = Point::new_gx(&x);
    let p2 = Point::new_gx(&x.neg());
    assert_ne!(p1, p0);
    assert_ne!(p2, p0);
    let p31 = p1.add(&p2);
    let p32 = p2.add(&p1);
    let p33 = p1.add_gx(&x.neg());
    assert_eq!(p31, p0);
    assert_eq!(p32, p0);
    assert_eq!(p33, p0);

    // new random points multiply.
    let x1 = Scalar::new_rand(&mut rng);
    let x2 = Scalar::new_rand(&mut rng);
    let p1 = Point::new_gx(&x1).mul_x(&x2);
    let p2 = Point::new_gx(&x2).mul_x(&x1);
    let p0 = Point::new_gx(&x1.mul(&x2));
    assert_eq!(p1, p0);
    assert_eq!(p2, p0);
    assert_ne!(p0, ID.clone());

    // new random point multiply 0.
    let x = Scalar::new_rand(&mut rng);
    let p1 = Point::new_gx(&x).mul_x(&ZERO);
    let p2 = ID.mul_x(&x);
    assert_eq!(p1, ID.clone());
    assert_eq!(p2, ID.clone());

    // The curve group is of prime order, thus
    // no two nonzero elements multiplies to zero.
}

#[test]
#[allow(non_snake_case)]
fn test_points_fromto_bytes() {
    let mut RNG = rand::rng();
    let rng = &mut RNG;

    {
        let p = Point::new_gx(&Scalar::new_rand(rng));
        println!("short {}", p.to_hex33());
        println!("long {}", p.to_hex65());

        let buf1 = p.to_bytes33();
        assert_eq!(buf1.len(), 33);
        let p1 = Point::new_from_bytes(&buf1).unwrap();

        let buf2 = p.to_bytes65();
        assert_eq!(buf2.len(), 65);
        let p2 = Point::new_from_bytes(&buf2).unwrap();

        assert_eq!(p, p1);
        assert_eq!(p, p2);
    }

    {
        let p1 = Point::new_from_bytes(&Point::ID_BYTES33).unwrap();
        let p2 = Point::new_from_bytes(&Point::ID_BYTES65).unwrap();

        assert_eq!(ID.clone(), p1);
        assert_eq!(ID.clone(), p2);

        let p3 = Point::new_from_bytes(&p1.to_bytes33()).unwrap();
        let p4 = Point::new_from_bytes(&p2.to_bytes33()).unwrap();
        assert_eq!(ID.clone(), p3);
        assert_eq!(ID.clone(), p4);
    }
}
