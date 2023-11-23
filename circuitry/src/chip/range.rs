use crate::{enforcement::RangeOp, utils::decompose_into_dyn, witness::Witness};
use ff::PrimeField;
use halo2::circuit::Value;
use num_integer::Integer;

use super::Chip;

pub trait RangeChip<F: PrimeField + Ord>: Chip<RangeOp<F>, F> {
    fn range(&mut self, value: Value<F>, size: usize) -> Witness<F> {
        let witness = self.new_witness(value);

        let single = crate::enforcement::Range::new(witness, size);
        self.new_op(RangeOp::Single(single));
        witness
    }

    fn decompose(
        &mut self,
        value: Value<F>,
        word_size: usize,
        limb_size: usize,
    ) -> (Witness<F>, Vec<Witness<F>>) {
        assert!(limb_size > 0);
        assert!(word_size > 0);

        let (number_of_limbs, overflow_size) = word_size.div_rem(&limb_size);
        let number_of_limbs = number_of_limbs + if overflow_size > 0 { 1 } else { 0 };
        if number_of_limbs == 1 {
            let witness = self.range(value, word_size);
            (witness, vec![])
        } else {
            let limbs = value
                .map(|v| decompose_into_dyn::<F, F>(&v, number_of_limbs, limb_size))
                .transpose_vec(number_of_limbs);

            let limbs = limbs
                .iter()
                .map(|limb| self.new_witness(*limb))
                .collect::<Vec<Witness<F>>>();

            let value = self.new_witness(value);

            let overflow_size = (overflow_size > 0).then_some(overflow_size);

            let op =
                crate::enforcement::RangeLimbs::new(value, &limbs[..], limb_size, overflow_size);

            self.new_op(RangeOp::Limbs(op));

            (value, limbs)
        }
    }
}
