use crate::chip::IntegerChip;
use crate::integer::{Integer, Range, UnassignedInteger};
use circuitry::chip::first_degree::FirstDegreeChip;
use circuitry::chip::range::RangeChip;
use circuitry::{
    utils::{big_to_fe, big_to_fe_unsafe, decompose, fe_to_big},
    witness::{Scaled, Witness},
};
use ff::PrimeField;
use halo2::circuit::Value;

impl<
        W: PrimeField,
        N: PrimeField + Ord,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    > IntegerChip<W, N, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>
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
            &self.rns.max_remainder_limbs,
            Value::known(big),
            native,
        )
    }

    pub fn range<Chip: RangeChip<N> + FirstDegreeChip<N>>(
        &self,
        chip: &mut Chip,
        integer: UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        range: Range,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let max_values = self.rns.max_values(range);
        let last_limb_size = max_values.last().unwrap().bits() as usize;

        let limbs = integer
            .limbs()
            .iter()
            .enumerate()
            .map(|(i, limb)| {
                if i == NUMBER_OF_LIMBS - 1 {
                    chip.decompose(*limb, last_limb_size, SUBLIMB_SIZE).0
                } else {
                    chip.decompose(*limb, LIMB_SIZE, SUBLIMB_SIZE).0
                }
            })
            .collect::<Vec<_>>();

        let terms: Vec<Scaled<N>> = limbs
            .iter()
            .zip(self.rns.left_shifters.iter())
            .map(|(limb, base)| Scaled::new(limb, *base))
            .collect::<Vec<Scaled<N>>>();

        let native = chip.compose(&terms[..], N::ZERO);

        Integer::new(
            &limbs.try_into().unwrap(),
            &max_values,
            integer.big(),
            native,
        )
    }
}
