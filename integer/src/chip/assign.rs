use crate::chip::IntegerChip;
use crate::integer::{Integer, Range, UnassignedInteger};
use circuitry::chip::first_degree::FirstDegreeChip;
use circuitry::chip::range::RangeChip;
use circuitry::chip::Core;
use circuitry::stack::Stack;
use circuitry::{
    utils::{big_to_fe, big_to_fe_unsafe, fe_to_big},
    witness::{Scaled, Witness},
};
use ff::PrimeField;
use halo2::circuit::Value;

impl<W: PrimeField, N: PrimeField + Ord> IntegerChip<W, N> {
    pub fn register_constant(&self, stack: &mut Stack<N>, constant: &W) -> Integer<W, N> {
        let big = fe_to_big(constant);
        let native: N = big_to_fe(&big);

        let limbs = self
            .rns
            .decompose(&big)
            .iter()
            .map(big_to_fe_unsafe)
            .collect::<Vec<_>>();

        let limbs = limbs
            .iter()
            .map(|limb| stack.get_constant(*limb))
            .collect::<Vec<Witness<N>>>();

        let native = stack.get_constant(native);

        Integer::new(
            &limbs,
            &self.rns.max_remainder_limbs,
            Value::known(big),
            native,
            self.rns.limb_size,
        )
    }

    pub fn range(
        &self,
        stack: &mut Stack<N>,
        integer: &UnassignedInteger<W, N>,
        range: Range,
    ) -> Integer<W, N> {
        let max_values = self.rns.max_values(range);
        let last_limb_size = max_values.last().unwrap().bits() as usize;

        let limbs = integer
            .limbs()
            .iter()
            .enumerate()
            .map(|(i, limb)| {
                if i == self.rns.number_of_limbs - 1 {
                    stack.decompose(*limb, last_limb_size, self.sublimb_size).0
                } else {
                    stack
                        .decompose(*limb, self.rns.limb_size, self.sublimb_size)
                        .0
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
            &limbs,
            &max_values,
            integer.big(),
            native,
            self.rns.limb_size,
        )
    }
}
