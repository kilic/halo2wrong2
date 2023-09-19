use ff::PrimeField;
use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::ops::Shl;

pub fn modulus<F: PrimeField>() -> BigUint {
    fe_to_big(&-F::one()) + 1usize
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

pub fn compose<const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>(
    input: &[BigUint; NUMBER_OF_LIMBS],
) -> BigUint {
    input
        .iter()
        .rev()
        .fold(BigUint::zero(), |acc, val| (acc << LIMB_SIZE) + val)
}

pub fn compose_dyn(input: Vec<BigUint>, limb_size: usize) -> BigUint {
    input
        .iter()
        .rev()
        .fold(BigUint::zero(), |acc, val| (acc << limb_size) + val)
}

pub fn compose_into<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
>(
    input: &[N; NUMBER_OF_LIMBS],
) -> W {
    let shifter = BigUint::one() << LIMB_SIZE;
    let shifter: W = big_to_fe_unsafe(&shifter);
    input.iter().rev().fold(W::zero(), |acc, val| {
        (acc * shifter) + fe_to_fe_unsafe::<W, N>(val)
    })
}

pub fn decompose<const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>(
    e: &BigUint,
) -> [BigUint; NUMBER_OF_LIMBS] {
    let mask = &(BigUint::one().shl(LIMB_SIZE) - 1usize);
    (0usize..)
        .step_by(LIMB_SIZE)
        .take(NUMBER_OF_LIMBS)
        .map(|shift| ((e >> shift) & mask))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

pub fn decompose_dyn(e: &BigUint, number_of_limbs: usize, limb_size: usize) -> Vec<BigUint> {
    let mask = &(BigUint::one().shl(limb_size) - 1usize);
    (0usize..)
        .step_by(limb_size)
        .take(number_of_limbs)
        .map(|shift| ((e >> shift) & mask))
        .collect::<Vec<_>>()
}

pub fn decompose_into<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
>(
    e: &W,
) -> [N; NUMBER_OF_LIMBS] {
    let big = &fe_to_big(e);
    decompose::<NUMBER_OF_LIMBS, LIMB_SIZE>(big)
        .iter()
        .map(|x| big_to_fe_unsafe(x))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

pub fn decompose_into_dyn<W: PrimeField, N: PrimeField>(
    e: &W,
    number_of_limbs: usize,
    limb_size: usize,
) -> Vec<N> {
    let big = &fe_to_big(e);
    decompose_dyn(big, number_of_limbs, limb_size)
        .iter()
        .map(big_to_fe)
        .collect::<Vec<_>>()
}

fn get_bits_128(segment: usize, window: usize, bytes: &[u8]) -> u128 {
    let skip_bits = segment * window;
    let skip_bytes = skip_bits / 8;
    let mut v = [0; 16];
    for (v, o) in v.iter_mut().zip(bytes[skip_bytes..].iter()) {
        *v = *o;
    }
    (u128::from_le_bytes(v) << (skip_bits - (skip_bytes * 8))) & ((1 << window) - 1)
}

// pub fn decompose_127_into<
//     W: PrimeField,
//     N: PrimeField,
//     const NUMBER_OF_LIMBS: usize,
//     const LIMB_SIZE: usize,
// >(
//     e: &W,
// ) -> [N; NUMBER_OF_LIMBS] {
//     #[cfg(feature = "sanity-checks")]
//     {
//         assert!(LIMB_SIZE <= 127);
//     }
//     let repr = e.to_repr();
//     (0..NUMBER_OF_LIMBS)
//         .map(|i| {
//             let u = get_bits_128(i, LIMB_SIZE, repr.as_ref());
//             N::from_u128(u)
//         })
//         .collect::<Vec<_>>()
//         .try_into()
//         .unwrap()
// }

fn get_bits_64(segment: usize, window: usize, bytes: &[u8]) -> u64 {
    let skip_bits = segment * window;
    let skip_bytes = skip_bits / 8;
    let mut v = [0; 8];
    for (v, o) in v.iter_mut().zip(bytes[skip_bytes..].iter()) {
        *v = *o;
    }
    (u64::from_le_bytes(v) << (skip_bits - (skip_bytes * 8))) & ((1 << window) - 1)
}

pub fn decompose_63_into<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
>(
    e: &W,
) -> [N; NUMBER_OF_LIMBS] {
    #[cfg(feature = "sanity-checks")]
    {
        assert!(LIMB_SIZE <= 63);
    }
    let repr = e.to_repr();
    (0..NUMBER_OF_LIMBS)
        .map(|i| get_bits_64(i, LIMB_SIZE, repr.as_ref()).into())
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

#[cfg(test)]
mod test {
    use crate::halo2::halo2curves::pasta::{Fp, Fq};
    use ff::PrimeField;
    use rand_core::OsRng;

    use crate::utils::{compose, compose_into, decompose_dyn};

    use super::{decompose, decompose_into, decompose_into_dyn, fe_to_big};

    fn run_test_compostion<
        W: PrimeField,
        N: PrimeField,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
    >() {
        for _ in 0..100000 {
            let e0 = W::random(OsRng);

            let u0 = decompose_into_dyn::<W, N>(&e0, NUMBER_OF_LIMBS, LIMB_SIZE);
            let u1 = decompose_into::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>(&e0);
            assert_eq!(u0, u1);
            // let u2 = decompose_127_into::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>(&e0);
            // assert_eq!(u0, u2);
            // let e1: W = compose_into::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>(&u2);
            // assert_eq!(e0, e1);

            let e0 = W::random(OsRng);
            let e0 = fe_to_big(&e0);
            let u0 = decompose_dyn(&e0, NUMBER_OF_LIMBS, LIMB_SIZE);
            let u1 = decompose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&e0);
            assert_eq!(u0, u1);
            let e1 = compose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&u1);
            assert_eq!(e0, e1);
        }
    }

    #[test]
    fn test_composition() {
        run_test_compostion::<Fp, Fq, 3, 88>()
    }
}
