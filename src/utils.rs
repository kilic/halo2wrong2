use ff::PrimeField;
use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::ops::Shl;

pub fn modulus<F: PrimeField>() -> BigUint {
    fe_to_big(&-F::ONE) + 1usize
}

pub fn power_of_two<F: PrimeField>(n: usize) -> F {
    let u = BigUint::one() << n;
    big_to_fe(&u)
}

pub fn big_to_fe<F: PrimeField>(e: &BigUint) -> F {
    let modulus = modulus::<F>();
    let e = e % modulus;
    big_to_fe_unsafe(&e)
}

pub fn big_to_fe_unsafe<F: PrimeField>(e: &BigUint) -> F {
    let bytes = e.to_bytes_le();
    let mut repr = F::Repr::default();
    repr.as_mut()[..bytes.len()].copy_from_slice(&bytes[..]);
    F::from_repr(repr).unwrap()
}

pub fn fe_to_big<F: PrimeField>(fe: &F) -> BigUint {
    BigUint::from_bytes_le(fe.to_repr().as_ref())
}

pub fn invert<F: PrimeField>(big: &BigUint) -> BigUint {
    fe_to_big(&big_to_fe::<F>(big).invert().unwrap())
}

pub fn fe_to_fe<W: PrimeField, N: PrimeField>(input: &N) -> W {
    let input = fe_to_big(input);
    big_to_fe(&input)
}

fn fe_to_fe_unsafe<W: PrimeField, N: PrimeField>(input: &N) -> W {
    let bytes = input.to_repr();
    let bytes = bytes.as_ref();
    let mut repr = W::Repr::default();
    repr.as_mut()[..bytes.len()].copy_from_slice(bytes);
    W::from_repr(repr).unwrap()
}

pub fn compose(input: &[BigUint], limb_size: usize) -> BigUint {
    input
        .iter()
        .rev()
        .fold(BigUint::zero(), |acc, val| (acc << limb_size) + val)
}

pub fn compose_into<W: PrimeField, N: PrimeField>(input: &[N], limb_size: usize) -> W {
    let shifter = BigUint::one() << limb_size;
    let shifter: W = big_to_fe_unsafe(&shifter);
    input.iter().rev().fold(W::ZERO, |acc, val| {
        (acc * shifter) + fe_to_fe_unsafe::<W, N>(val)
    })
}

pub fn decompose(e: &BigUint, number_of_limbs: usize, limb_size: usize) -> Vec<BigUint> {
    let mask = &(BigUint::one().shl(limb_size) - 1usize);
    (0usize..)
        .step_by(limb_size)
        .take(number_of_limbs)
        .map(|shift| ((e >> shift) & mask))
        .collect::<Vec<_>>()
}

pub fn decompose_into<W: PrimeField, N: PrimeField>(
    e: &W,
    number_of_limbs: usize,
    limb_size: usize,
) -> Vec<N> {
    let big = &fe_to_big(e);
    decompose(big, number_of_limbs, limb_size)
        .iter()
        .map(big_to_fe)
        .collect::<Vec<_>>()
}

#[cfg(test)]
mod test {

    use super::{decompose, decompose_into, fe_to_big};
    use crate::utils::{compose, compose_into};
    use ff::PrimeField;
    use halo2::halo2curves::pasta::{Fp, Fq};
    use num_integer::div_ceil;
    use rand_core::OsRng;

    fn run_test_compostion<W: PrimeField, N: PrimeField>(limb_size: usize) {
        let wrong_modulus = &super::modulus::<W>();
        let number_of_limbs = div_ceil(wrong_modulus.bits() as usize, limb_size);

        for _ in 0..100000 {
            let e0 = W::random(OsRng);

            let u0 = decompose_into::<W, N>(&e0, number_of_limbs, limb_size);
            let e1: W = compose_into::<W, N>(&u0, limb_size);
            assert_eq!(e0, e1);

            let e0 = W::random(OsRng);
            let e0 = fe_to_big(&e0);
            let u0 = decompose(&e0, number_of_limbs, limb_size);
            let e1 = compose(&u0, limb_size);
            assert_eq!(e0, e1);
        }
    }

    #[test]
    fn test_composition() {
        run_test_compostion::<Fp, Fq>(88)
    }
}
