use crate::{
    enforcement::FirstDegreeComposition,
    utils::{decompose_into, decompose_into_dyn},
    witness::{Composable, Scaled, Witness},
};
use ff::PrimeField;
use halo2::circuit::Value;
use num_integer::Integer;

use super::Chip;

pub trait FirstDegreeChip<F: PrimeField + Ord>: Chip<FirstDegreeComposition<F>, F> {
    fn decompose_generic(
        &mut self,
        value: Value<F>,
        word_size: usize,
        limb_size: usize,
    ) -> (Witness<F>, Vec<Witness<F>>) {
        assert!(word_size > limb_size);
        assert!(word_size > 1);

        let (number_of_limbs, overflow_bit_size) = word_size.div_rem(&limb_size);
        let number_of_limbs = number_of_limbs + if overflow_bit_size > 0 { 1 } else { 0 };

        let limbs = value
            .map(|v| decompose_into_dyn::<F, F>(&v, number_of_limbs, limb_size))
            .transpose_vec(number_of_limbs);

        let bases = self.bases(limb_size)[..number_of_limbs].to_vec();

        let limbs = limbs
            .iter()
            .enumerate()
            .map(|(i, limb)| {
                let bit_size = if i == number_of_limbs - 1 && overflow_bit_size != 0 {
                    overflow_bit_size
                } else {
                    limb_size
                };
                self.new_witness_in_range(*limb, bit_size)
            })
            .collect::<Vec<Witness<F>>>();

        let value = self.new_witness(value);

        let terms: Vec<Scaled<_>> = limbs
            .iter()
            .zip(bases.iter())
            .map(|(coeff, base)| Scaled::new(coeff, *base))
            .chain(std::iter::once(Scaled::sub(&value)))
            .collect();

        self.zero_sum(&terms[..], F::zero());

        (value, limbs)
    }

    fn decompose<const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>(
        &mut self,
        value: Value<F>,
    ) -> (Witness<F>, [Witness<F>; NUMBER_OF_LIMBS]) {
        let limbs = value
            .map(|value| decompose_into::<F, F, NUMBER_OF_LIMBS, LIMB_SIZE>(&value))
            .transpose_array();

        let bases = self.bases(LIMB_SIZE)[..NUMBER_OF_LIMBS].to_vec();

        let limbs = limbs
            .iter()
            .map(|limb| self.new_witness_in_range(*limb, LIMB_SIZE))
            .collect::<Vec<Witness<F>>>();

        let value = self.new_witness(value);

        let terms: Vec<Scaled<_>> = limbs
            .iter()
            .zip(bases.iter())
            .map(|(coeff, base)| Scaled::new(coeff, *base))
            .chain(std::iter::once(Scaled::sub(&value)))
            .collect();

        self.zero_sum(&terms[..], F::zero());

        (value, limbs.try_into().unwrap())
    }

    fn equal_to_constant(&mut self, w0: &Witness<F>, constant: F) {
        self.zero_sum(&[w0.add()], -constant);
    }

    fn assert_zero(&mut self, w0: &Witness<F>) {
        self.equal_to_constant(w0, F::zero())
    }

    fn assert_one(&mut self, w0: &Witness<F>) {
        self.equal_to_constant(w0, F::one())
    }

    fn add(&mut self, w0: &Witness<F>, w1: &Witness<F>) -> Witness<F> {
        let u = self.new_witness(w0.value() + w1.value());
        self.zero_sum(&[w0.add(), w1.add(), u.sub()], F::zero());
        u
    }

    fn add_constant(&mut self, w0: &Witness<F>, constant: F) -> Witness<F> {
        let u = w0.value().map(|w0| w0 + constant);
        let u = self.new_witness(u);
        self.zero_sum(&[w0.add(), u.sub()], constant);
        u
    }

    fn add_scaled(&mut self, w0: &Scaled<F>, w1: &Scaled<F>) -> Witness<F> {
        let u = self.new_witness(w0.value() + w1.value());
        self.zero_sum(&[*w0, *w1, u.sub()], F::zero());

        u
    }

    fn sub(&mut self, w0: &Witness<F>, w1: &Witness<F>) -> Witness<F> {
        let u = self.new_witness(w0.value() - w1.value());
        self.zero_sum(&[w0.add(), w1.sub(), u.sub()], F::zero());
        u
    }

    fn sub_and_add_constant(
        &mut self,
        w0: &Witness<F>,
        w1: &Witness<F>,
        constant: F,
    ) -> Witness<F> {
        let u = (w0.value() - w1.value()).map(|dif| dif + constant);
        let u = self.new_witness(u);
        self.zero_sum(&[w0.add(), w1.sub(), u.sub()], constant);
        u
    }

    fn sub_from_constant(&mut self, constant: F, w1: &Witness<F>) -> Witness<F> {
        let u = w1.value().map(|w1| constant - w1);
        let u = self.new_witness(u);
        self.zero_sum(&[w1.sub(), u.sub()], constant);

        u
    }

    fn scale(&mut self, w: Scaled<F>) -> Witness<F> {
        let u = self.new_witness(w.value());
        self.zero_sum(&[w, u.sub()], F::zero());
        u
    }

    fn zero_sum(&mut self, terms: &[Scaled<F>], constant_to_add: F) {
        let terms: Vec<Scaled<F>> = terms.iter().filter(|e| !e.is_empty()).cloned().collect();

        assert!(!terms.is_empty());

        #[cfg(feature = "prover-sanity")]
        {
            let result = Scaled::compose(&terms[..], constant_to_add);
            result.map(|must_be_zero| {
                assert_eq!(must_be_zero, F::zero());
            });
        }

        let composition = FirstDegreeComposition::new(terms, constant_to_add);
        self.new_op(composition);
    }

    fn compose(&mut self, terms: &[Scaled<F>], constant_to_add: F) -> Witness<F> {
        // TODO: don't allow empty terms
        let mut terms: Vec<Scaled<F>> = terms.iter().filter(|e| !e.is_empty()).cloned().collect();
        assert!(!terms.is_empty());
        let result = Scaled::compose(&terms[..], constant_to_add);
        let result = self.new_witness(result).sub();
        terms.push(result);
        let composition = FirstDegreeComposition::new_no_range(terms, constant_to_add);
        self.new_op(composition);
        result.witness
    }
}
