use crate::chip::IntegerChip;
use crate::integer::{Integer, Range, UnassignedInteger};
use circuitry::chip::first_degree::FirstDegreeChip;
use circuitry::{
    utils::{big_to_fe, big_to_fe_unsafe, decompose, fe_to_big},
    witness::{Scaled, Witness},
};
use ff::PrimeField;
use halo2::circuit::Value;
use num_bigint::BigUint;
use num_traits::One;

impl<
        W: PrimeField,
        N: PrimeField + Ord,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const NUMBER_OF_SUBLIMBS: usize,
        const SUBLIMB_SIZE: usize,
    > IntegerChip<W, N, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>
{
    pub fn register_constant(
        &self,
        stack: &mut impl FirstDegreeChip<N>,
        constant: &W,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let big = fe_to_big(constant);
        let native: N = big_to_fe(&big);

        let limbs: [N; NUMBER_OF_LIMBS] = decompose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&big)
            .iter()
            .map(big_to_fe_unsafe)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let limbs = limbs
            .iter()
            .map(|limb| stack.get_constant(*limb))
            .collect::<Vec<Witness<N>>>();

        let native = stack.get_constant(native);

        Integer::new(
            &limbs.try_into().unwrap(),
            &self.rns.max_values(Range::Remainder),
            Value::known(big),
            native,
        )
    }

    pub fn range(
        &self,
        stack: &mut impl FirstDegreeChip<N>,
        integer: UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        range: Range,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let max = (BigUint::one() << LIMB_SIZE) - 1usize;
        let mut max_values = vec![max; NUMBER_OF_LIMBS - 1];
        let (last_limb_max, last_limb_size) = self.rns.last_limb_max(range);
        max_values.push(last_limb_max);

        let limbs = integer
            .limbs()
            .transpose_vec(NUMBER_OF_LIMBS)
            .iter()
            .enumerate()
            .map(|(i, limb)| {
                if i == NUMBER_OF_LIMBS - 1 {
                    stack
                        .decompose_generic(*limb, last_limb_size, SUBLIMB_SIZE)
                        .0
                } else {
                    stack.decompose::<NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>(*limb).0
                }
            })
            .collect::<Vec<_>>();

        let terms: Vec<Scaled<N>> = limbs
            .iter()
            .zip(self.rns.left_shifters.iter())
            .map(|(limb, base)| Scaled::new(limb, *base))
            .collect::<Vec<Scaled<N>>>();

        let native = stack.compose(&terms[..], N::ZERO);

        Integer::new(
            &limbs.try_into().unwrap(),
            &max_values.try_into().unwrap(),
            integer.big(),
            native,
        )
    }
}
