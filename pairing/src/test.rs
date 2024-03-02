use circuitry::{chip::first_degree::FirstDegreeChip, stack::Stack};
use ff::Field;
use halo2::{
    circuit::Value,
    halo2curves::bn256::{Fr, G1Affine, G2Affine},
};
use integer::rns::Rns;
use rand_core::OsRng;

use crate::PairingChip;

fn make_stack() -> Stack<Fr> {
    let mut acc = Fr::ZERO;
    let n = 2;

    let mut g1: Vec<G1Affine> = vec![];
    let mut g2: Vec<G2Affine> = vec![];

    for _ in 0..n - 1 {
        let s1 = Fr::random(OsRng);
        let s2 = Fr::random(OsRng);
        acc += s1 * s2;
        g1.push((G1Affine::generator() * s1).into());
        g2.push((G2Affine::generator() * s2).into());
    }

    g1.push((G1Affine::generator() * -acc).into());
    g2.push(G2Affine::generator());

    let rns: Rns<_, Fr, 3, 90> = Rns::construct();
    let ch: PairingChip<Fr, 3, 90, 18> = PairingChip::new(&rns);

    let stack = &mut Stack::default();
    let g1 = g1
        .iter()
        .map(|g1| ch.assign_point1(stack, Value::known(*g1)))
        .collect::<Vec<_>>();

    let g2 = g2
        .iter()
        .map(|g2| ch.assign_point2(stack, Value::known(*g2)))
        .collect::<Vec<_>>();

    let res = ch.pairing_check(stack, g1, g2);
    stack.assert_one(&res);

    stack.clone()
}

#[test]
fn test_pairing() {
    make_stack();
}
