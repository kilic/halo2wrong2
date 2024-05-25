use ff::{Field, PrimeField};
use group::prime::PrimeCurveAffine;
use halo2::halo2curves::bn256::{self, Fq, Fq12};
use halo2::halo2curves::bn256::{Fq2, G1Affine, G2Affine, FROBENIUS_COEFF_FQ6_C1};
use num_bigint::BigUint;
use num_traits::Num;

fn eval(f: &mut Fq12, lambda: Fq2, p1: &G1Affine, t_x: Fq2, t_y: Fq2) {
    // let c1 = lambda.mul_by_fq(&p1.x);
    // let c3 = (lambda * t_x - t_y).mul_by_fq(&p1.y);
    // f.sparse_mul(&c1, &c3);

    let c1 = Fq2::new(lambda.c0 * &p1.x, lambda.c1 * &p1.x);

    let t = lambda * t_x - t_y;
    let c3 = Fq2::new(t.c0 * &p1.y, t.c1 * &p1.y);

    f.mul_by_034(&bn256::Fq2::one(), &c1, &c3);
}

pub(crate) fn double(acc: &mut G2Affine) -> Fq2 {
    let x2 = acc.x.square();
    let t0 = x2.double() + x2;
    let t1 = acc.y.double().invert().unwrap();
    let lambda = t0 * t1;
    let x3 = lambda.square() - acc.x.double();
    let y3 = lambda * (acc.x - x3) - acc.y;

    acc.x = x3;
    acc.y = y3;
    lambda
}

fn double_eval(f: &mut Fq12, acc: &mut G2Affine, p1: &G1Affine) {
    let G2Affine { x: t_x, y: t_y } = *acc;
    let lambda = double(acc);

    eval(f, lambda, p1, t_x, t_y);
}

pub(crate) fn add(acc: &mut G2Affine, p2: &G2Affine, neg: bool) -> Fq2 {
    let t0 = if neg { acc.y + p2.y } else { acc.y - p2.y };
    let t1 = (acc.x - p2.x).invert().unwrap();
    let lambda = t0 * t1;
    let x3 = lambda.square() - acc.x - p2.x;
    let y3 = lambda * (acc.x - x3) - acc.y;

    acc.x = x3;
    acc.y = y3;
    lambda
}

fn add_eval(f: &mut Fq12, acc: &mut G2Affine, p2: &G2Affine, p1: &G1Affine, neg: bool) {
    let G2Affine { x: t_x, y: t_y } = *acc;
    let lambda = add(acc, p2, neg);

    eval(f, lambda, p1, t_x, t_y);
}

pub(crate) fn miller_loop(p1: &[G1Affine], p2: &[G2Affine]) -> Fq12 {
    let terms = p1
        .iter()
        .zip(p2.iter())
        .map(|(p1, p2)| {
            assert!(!bool::from(p1.is_identity()));
            assert!(!bool::from(p2.is_identity()));
            let y = p1.y.invert().unwrap();
            let x = (p1.x * y).neg();
            (G1Affine { x, y }, p2)
        })
        .collect::<Vec<_>>();

    let mut f = Fq12::one();
    let mut acc = terms.iter().map(|(_, q)| (*q).clone()).collect::<Vec<_>>();

    super::SIX_U_PLUS_2_NAF
        .iter()
        .rev()
        .skip(1)
        .enumerate()
        .for_each(|(i, x)| {
            (i != 0).then(|| f.square_assign());

            terms
                .iter()
                .zip(acc.iter_mut())
                .for_each(|((g1, _), acc)| double_eval(&mut f, acc, g1));

            match x {
                val @ (1 | -1) => {
                    terms.iter().zip(acc.iter_mut()).for_each(|((g1, q), r)| {
                        add_eval(&mut f, r, q, g1, val.is_negative());
                    });
                }

                _ => {}
            }
        });

    terms.iter().zip(acc.iter_mut()).for_each(|((p, q), acc)| {
        let mut q1: G2Affine = (*q).clone();
        q1.x.conjugate();
        q1.x.mul_assign(&FROBENIUS_COEFF_FQ6_C1[1]);
        q1.y.conjugate();
        q1.y.mul_assign(&super::XI_TO_Q_MINUS_1_OVER_2);
        add_eval(&mut f, acc, &q1, p, false);
    });

    terms.iter().zip(acc.iter_mut()).for_each(|((p, q), acc)| {
        let mut minusq2: G2Affine = (*q).clone();
        minusq2.x.mul_assign(&FROBENIUS_COEFF_FQ6_C1[2]);
        add_eval(&mut f, acc, &minusq2, p, false);
    });

    f
}

pub(crate) fn final_exp_witness(p1: &[G1Affine], p2: &[G2Affine]) -> (Fq12, usize) {
    let f = miller_loop(&p1, &p2);

    #[cfg(feature = "prover-sanity")]
    {
        // naive final exp

        let h = BigUint::from_str_radix(
            "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47",
            16,
        )
        .unwrap();
        let h = h.pow(12) - 1usize;

        let r = &BigUint::from_str_radix(
            "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001",
            16,
        )
        .unwrap();
        let h = h / r;
        assert_eq!(f.pow(h.to_u64_digits()), bn256::Fq12::one());
    }

    let c0 = rth_root(&f);
    let c1 = mth_root(&c0);
    let (c, u) = cube_root_with_shift(&c1);

    (c, u)
}

// TODO: optimize exp
const CUBE_NON_RES_EXP: [u64; 48] = [
    0xeb46f64643825060,
    0xc09504ce57838ff3,
    0xb6973b1dfda111a7,
    0x9e6a6b1d46fc408c,
    0x745bdaf039c199f6,
    0xe9f65a41395df713,
    0x4dcd3d267739953c,
    0x9f49699c7d2e3b27,
    0xb189f37c0ecd514e,
    0x55aa926463b3f1ad,
    0x6030fad438f67304,
    0x1dc6e7821edb8a5c,
    0x3fabe2a396c821ee,
    0xce442caa65704817,
    0xac5266c00ed4ded7,
    0x53aa9ef14c0ae51f,
    0x133df7ebbc224e97,
    0x88ce9faea263de92,
    0x8c4be6bdd2b88017,
    0x628d5a19e9c247d9,
    0xa93bf3094d3d5518,
    0x3939f77b19cd8e05,
    0x3c85c4759d907006,
    0xf47559371ceb7cb4,
    0x9868d7443cc60fe8,
    0x591589f02cf8ecb7,
    0x680fa342f7100bba,
    0xb44b431aae371e85,
    0x99625bea8196289d,
    0xa38d36e079b35749,
    0x08d38b7277eb44ec,
    0xb5de835af494b061,
    0x370bd1df6206ad8e,
    0xf755226d1fb5139f,
    0xedafa93168993756,
    0x5b43e8559e471ed9,
    0xe84ed08d6375382d,
    0x9b99a5c06b47a88a,
    0x19e45304da068978,
    0x12aff3b863cdce2f,
    0xb0178e622c3aaf92,
    0x19e6b3b6373de8df,
    0xeb4cec3eff8e12f1,
    0xc3fc152a73114859,
    0xd516d062f8015f36,
    0x6440dd3153897c68,
    0x73924a5d67a5d259,
    0x00000002fae42e49,
];

// TODO: optimize exp
const CUBE_CLEAR_EXP: [u64; 48] = [
    0x7102a0d331e861cb,
    0x1a187b6ff0473e38,
    0xcddfacdb2f51d13f,
    0x483cd48f4e7b1ed5,
    0xd4e6f5255778f2bd,
    0x83ecae026a6bc6c7,
    0x911a907caf15187d,
    0xe9747f2bb8c8d2c8,
    0x069354deab370302,
    0x61fcd603b7d741d7,
    0xcaac7b1157716c8e,
    0xb540417698d8b945,
    0x6aa78d2280d80141,
    0x4a028665203390e4,
    0x6eadb7f42679a970,
    0x586e9d9728be087c,
    0xedbfecbce10ac08a,
    0x1807a7196e4f8cfb,
    0xdf452e78ceea638f,
    0xb7cc58aba05c8766,
    0xb0ef41e3e66a915f,
    0x3b02259c43537709,
    0x31a623b881185000,
    0x4b6ca47d4cec46fd,
    0xd63cc59a3b23c7b3,
    0x7513c2bd0b25a9f3,
    0xdded9dc01c1d09ea,
    0xcdc9e60a783aee2a,
    0x9d62752e9c80d218,
    0x944799bc7649033b,
    0xed5d2b1733d94e67,
    0x19b2e86baa3e6558,
    0xe5982437ae4c1964,
    0xffadd1de1d9e6905,
    0x253f6514cafc3174,
    0x58b6a9ca483b85e2,
    0xe2ad95f2460dd2ac,
    0x8a80f32d0d746e89,
    0xe483b739118e76de,
    0x4c8b41ea6282e1b5,
    0x81c7fbcabf448b3e,
    0x4ccfa7d757611b96,
    0x2528c66125e8d14b,
    0x6612d16063139a62,
    0xd87c1aae55098844,
    0x628724a303180e16,
    0x33b015b79b8ae1dd,
    0x000000001c41570c,
];

pub fn rth_root(e: &Fq12) -> Fq12 {
    // TODO: optimize exp
    const R_PRIME: [u64; 44] = [
        0xa11b194379daaca1,
        0xa5f0d2dcad831751,
        0x2b410d5c2e47c1b4,
        0x384a4274ed212efc,
        0x70aac1f263098d89,
        0x00f5fd95b7c6784e,
        0x7ebfe5d9a66b49bb,
        0x1c4d0568f9a146bb,
        0xc647b55ab5455a1f,
        0x315372b248a33b03,
        0xaa284fca9651ce25,
        0x1f401dc214ffb6d3,
        0x65cfacd3e5294c64,
        0xcce86cb5c9a967d9,
        0xd457e4e53e766cdf,
        0xc3c33ad27ef8286d,
        0xb0c4571cbda9e9b9,
        0x026024e519498470,
        0xb517826e8d0a7ea3,
        0xfe0b42fd3f9e4cb6,
        0xdf7db6f0f880457b,
        0x182418ed6397d5da,
        0x4dbb3c5f77a5e53d,
        0xd8252918fdce3f1e,
        0xfd9bd55b098443f5,
        0xf8a2e6743a1e2509,
        0xfe45c6ba38a2a7d2,
        0x379e03a9a5e228c5,
        0xc190b44c4eaa05ef,
        0xe326d9499c2238ca,
        0x068e0b9719edade8,
        0x51acfb2c2b91395f,
        0x23575e4b046e4551,
        0x28206b1dd3e111f2,
        0xee7b16d7001a28fd,
        0xcc9f2cef8aa8b968,
        0x82165fad421d6efa,
        0xe0d2744ba5f78583,
        0xa5fa4275e36247c2,
        0x847f3dae4767238b,
        0x4c2fca934b0d67ba,
        0xf17857b96814f37b,
        0x79815b691a6a294e,
        0x0000002a71a42aee,
    ];
    e.pow(R_PRIME)
}

pub fn mth_root(e: &Fq12) -> Fq12 {
    // TODO: optimize exp
    const M_PRIME_PRIME: [u64; 44] = [
        0xf7721c7aff2f56b7,
        0xa41c1525e62392af,
        0xf08969a9108c577f,
        0x843248b70bc58b9b,
        0x072d7a403a1e679c,
        0x88c5e5a473bf4dc0,
        0x51c8b0e8579cc523,
        0xb459b999d3ac8a7d,
        0x18fa924d8034a528,
        0xc55e1e6afd4f17a6,
        0xb3667969b57a1a59,
        0x38188d68645ec977,
        0x4ce226be79e0093e,
        0x93f8674a5444d2ec,
        0x111b573624f772f3,
        0x349070d501f354a4,
        0xff1e01c9b766a835,
        0x4d90962b1fc6ee8f,
        0xb6fe4cd038239172,
        0xe82a55d5a62a0447,
        0x2ddd7fea7f5d2359,
        0xeebee1afc60f5209,
        0x8a10190cff16e8e4,
        0x9d001574cb7631fa,
        0x0d0f5585b4ca70cc,
        0x496f56776b19ac89,
        0x91f3035f8757e549,
        0xfd3d06751c3e97a3,
        0xe51a66ac9a83c506,
        0xdf0ea52e1e84aa13,
        0xce20f6fcdca29467,
        0x8591195a1879549f,
        0x5261846036719b2e,
        0xdec7495884c546a9,
        0x2d6eb7558005a1ee,
        0xe534278298cad674,
        0xa29b3e0abf45fbcb,
        0x0bd4341f0e9cc796,
        0xf544c6143b686a58,
        0x5d32122cd9a4aa34,
        0xadc0eee93555b6d4,
        0x715424f40cb25186,
        0x8dd1549b7e60deaa,
        0x0000000186f601e0,
    ];

    e.pow(M_PRIME_PRIME)
}

fn is_cube_nonresidue(e: &Fq12) -> bool {
    e.pow(CUBE_NON_RES_EXP) != Fq12::one()
}

pub(crate) fn w1() -> Fq12 {
    // TODO: make constant

    let mut w = Fq12::zero();

    w.c0.c2.c0 = bn256::Fq::from_str_vartime(
        "2268774813928168705714769340309076012973838184912660903371022264081608589547",
    )
    .unwrap();
    w.c0.c2.c1 = Fq::from_str_vartime(
        "4505553186665064976568408494606738900088290417616355650737309862368100888609",
    )
    .unwrap();

    w
}

pub(crate) fn w2() -> Fq12 {
    // TODO: make constant

    w1() * w1()
}

pub(crate) fn cube_root_with_shift(e: &Fq12) -> (Fq12, usize) {
    if !is_cube_nonresidue(e) {
        return (cube_root(e).unwrap(), 0);
    }

    let a = e * w1();
    if !is_cube_nonresidue(&a) {
        return (cube_root(&a).unwrap(), 1);
    }

    let a = e * w2();
    if !is_cube_nonresidue(&a) {
        return (cube_root(&a).unwrap(), 2);
    }

    unreachable!();
}

pub(crate) fn cube_root(e: &Fq12) -> Option<Fq12> {
    let w = w1();

    let mut a = e.pow(CUBE_CLEAR_EXP);

    for _ in 0..27 {
        if (a * a * a) == *e {
            return Some(a);
        }
        a = a * w;
    }

    None
}

#[cfg(test)]
#[test]
fn cube_root_setup() {
    fn divides(a: &BigUint, b: &BigUint) -> BigUint {
        use num_integer::Integer;
        use num_traits::Zero;
        let (q, rem) = a.div_rem(b);
        assert_eq!(rem, BigUint::zero());
        q
    }

    use halo2::halo2curves::bn256::{Fq, Fq12, Fq6};
    use num_integer::Integer;
    use num_traits::Zero;
    use rand_core::OsRng;

    let three: &BigUint = &3usize.into();

    let q = &BigUint::from_str_radix(
        "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47",
        16,
    )
    .unwrap();
    let q12 = q.pow(12);
    let minus_one = &(q12 - 1usize);
    let exp_non_res = &divides(minus_one, three);

    println!("exp non res:");
    exp_non_res
        .to_u64_digits()
        .iter()
        .for_each(|limb| println!("0x{:016x?},", limb));

    let (t, s) = &{
        let mut s: u32 = 0;
        let mut t = minus_one.clone();
        loop {
            let (u, rem) = t.div_rem(three);
            if rem != BigUint::zero() {
                break;
            }
            t = u;
            s += 1;
        }
        assert_eq!(minus_one, &(&t * three.pow(s)));
        (t, s)
    };

    println!("t: {}", t.to_str_radix(16));
    assert_eq!(*s, 3);

    let exp_clear = &divides(&(t + 1usize), three);
    println!("exp clear:");
    exp_clear
        .to_u64_digits()
        .iter()
        .for_each(|limb| println!("0x{:016x?},", limb));

    let mut non_res = Fq12::zero();
    non_res.c0.c1.c0 = Fq::one();
    assert!(non_res.pow(exp_non_res.to_u64_digits()) != Fq12::one());
    // while non_res.pow(exp_non_res.to_u64_digits()) == Fq12::one() {
    //     non_res = non_res + Fq12::one();
    // }
    let w = non_res.pow(t.to_u64_digits());
    println!("w: {:#?}", w);

    assert!(w.c0.c0 == Fq2::zero());
    assert!(w.c0.c1 == Fq2::zero());
    assert!(w.c1 == Fq6::zero());

    println!("w020: {:#?}", w.c0.c2.c0);
    println!("w021: {:#?}", w.c0.c2.c1);

    let mut group = vec![];
    for _ in 0..27usize {
        let w_i = group.last().unwrap_or(&Fq12::one()) * w;
        group.iter().for_each(|g| assert_ne!(g, &w_i));
        group.push(w_i);
    }
    assert_eq!(group.last().unwrap(), &Fq12::one());

    for _ in 0..100 {
        let input = &Fq12::random(OsRng);

        let input = input * input * input;
        assert!(input.pow(exp_non_res.to_u64_digits()) == Fq12::one());

        let mut res = vec![];
        let mut a = input.pow(exp_clear.to_u64_digits());
        for _ in 0..27usize {
            (a * a * a == input).then(|| res.push(a.clone()));
            a = a * w;
        }

        assert_eq!(res.len(), 3);
        for res in res.iter() {
            assert_eq!(res * res * res, input);
        }
        assert_ne!(res[0], res[1]);
        assert_ne!(res[0], res[2]);
    }
}

#[test]
fn test_cuberoot() {
    use ff::Field;
    use rand_core::OsRng;

    let mut w = Fq12::zero();
    w.c0.c2.c0 = Fq::from_str_vartime(
        "2268774813928168705714769340309076012973838184912660903371022264081608589547",
    )
    .unwrap();
    w.c0.c2.c1 = Fq::from_str_vartime(
        "4505553186665064976568408494606738900088290417616355650737309862368100888609",
    )
    .unwrap();

    for _ in 0..100 {
        let a = Fq12::random(OsRng);

        {
            let a = a * a * a;
            assert!(!is_cube_nonresidue(&a));
            cube_root(&a).unwrap();
            assert!(is_cube_nonresidue(&(w * a)));
            assert!(is_cube_nonresidue(&(w * w * a)));
            assert!(!is_cube_nonresidue(&(w * w * w * a)));
        }

        if is_cube_nonresidue(&a) {
            let aw = a * w;
            let d0 = !is_cube_nonresidue(&aw);
            if d0 {
                let curt = cube_root(&aw).unwrap();
                assert_eq!(curt * curt * curt, aw);
            }
            let aw2 = a * w * w;
            let d1 = !is_cube_nonresidue(&aw2);
            if d1 {
                let curt = cube_root(&aw2).unwrap();
                assert_eq!(curt * curt * curt, aw2);
            }
            assert!(d0 ^ d1);
        } else {
            let curt = cube_root(&a).unwrap();
            assert_eq!(curt * curt * curt, a);
        }
    }
}
