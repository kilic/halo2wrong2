use crate::circuitry::{enforcement::RangeOp, witness::Witness};
use crate::utils::{compose_into, decompose_into, fe_to_big};
use ff::PrimeField;
use halo2::circuit::Value;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::One;

use super::Chip;

pub trait RangeChip<F: PrimeField + Ord>: Chip<RangeOp<F>, F> {
    fn range(&mut self, value: Value<F>, size: usize) -> Witness<F> {
        let witness = self.new_witness(value);

        let single = crate::circuitry::enforcement::Range::new(witness, size);
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
            #[cfg(feature = "prover-sanity")]
            {
                witness.value.map(|value| {
                    let big = fe_to_big(&value);
                    assert!(big < BigUint::one() << word_size);
                });
            }
            (witness, vec![])
        } else {
            let limbs = value
                .map(|value| {
                    let decomposed = decompose_into::<F, F>(&value, number_of_limbs, limb_size);

                    #[cfg(feature = "prover-sanity")]
                    {
                        let _value: F = compose_into(&decomposed[..], limb_size);
                        assert_eq!(_value, value)
                    }

                    decomposed
                })
                .transpose_vec(number_of_limbs);

            let limbs = limbs
                .iter()
                .map(|limb| self.new_witness(*limb))
                .collect::<Vec<Witness<F>>>();

            let value = self.new_witness(value);

            let overflow_size = (overflow_size > 0).then_some(overflow_size);

            let op = crate::circuitry::enforcement::RangeLimbs::new(
                value,
                &limbs[..],
                limb_size,
                overflow_size,
            );

            self.new_op(RangeOp::Limbs(op));

            (value, limbs)
        }
    }
}
