use ff::Field;
use group::prime::PrimeCurveAffine;
use halo2::halo2curves::bls12381::Fq12;
use halo2::halo2curves::bls12381::{Fq2, G1Affine, G2Affine};

fn eval(f: &mut Fq12, lambda: Fq2, p1: &G1Affine, t_x: Fq2, t_y: Fq2) {
    let c1 = Fq2::new(lambda.c0 * &p1.x, lambda.c1 * &p1.x);
    let t = lambda * t_x - t_y;
    let c3 = Fq2::new(t.c0 * &p1.y, t.c1 * &p1.y);
    f.mul_by_014(&c3, &c1, &Fq2::one());
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
            // (p1, p2)
            let y = p1.y.invert().unwrap();
            let x = (p1.x * y).neg();
            (G1Affine { x, y }, p2)
        })
        .collect::<Vec<_>>();

    let mut f = Fq12::one();
    let mut acc = terms.iter().map(|(_, q)| (*q).clone()).collect::<Vec<_>>();

    for (i, x) in super::BLS_X.iter().map(|&b| b == 1).skip(1).enumerate() {
        (i != 0).then(|| f.square_assign());

        terms
            .iter()
            .zip(acc.iter_mut())
            .for_each(|((g1, _), acc)| double_eval(&mut f, acc, g1));

        if x {
            terms.iter().zip(acc.iter_mut()).for_each(|((g1, q), r)| {
                add_eval(&mut f, r, q, g1, false);
            });
        }
    }

    f.conjugate();

    f
}
