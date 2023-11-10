use circuitry::chip::first_degree::FirstDegreeChip;
use circuitry::chip::second_degree::SecondDegreeChip;
use circuitry::witness::{Composable, Scaled, Witness};
use ff::PrimeField;
use num_bigint::BigUint;
use num_traits::Zero;

use crate::chip::IntegerChip;
use crate::integer::{Integer, Range};

impl<
        W: PrimeField,
        N: PrimeField + Ord,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const NUMBER_OF_SUBLIMBS: usize,
        const SUBLIMB_SIZE: usize,
    > IntegerChip<W, N, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>
{
    pub fn reduce_new<Stack: SecondDegreeChip<N> + FirstDegreeChip<N>>(
        &self,
        stack: &mut Stack,
        integer: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let (result, quotient) = self.rns.reduction_witness(integer);

        let result = self.range(stack, result, Range::Remainder);
        let quotient = stack
            .decompose::<NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>(quotient)
            .0;

        let base = self.rns.rsh(1);
        let intermediate = integer
            .limbs()
            .iter()
            .zip(result.limbs().iter())
            .zip(self.rns.neg_wrong_limbs_in_binary.iter())
            .map(|((limb, r), w)| {
                vec![
                    quotient.scale(*w * *base),
                    limb.scale(*base),
                    r.scale(-*base),
                ]
            })
            .collect::<Vec<_>>();

        let mut carry_max = BigUint::zero();
        let max_carries = integer
            .max_vals()
            .iter()
            .take(self.rns.number_of_carries)
            .zip(self.rns.big_neg_wrong_limbs_in_binary.iter())
            .map(|(limb, w)| {
                let t = &self.rns.max_reduction_quotient * w + limb + &carry_max;
                carry_max = t >> LIMB_SIZE;
                carry_max.bits()
            });

        let mut carry: Option<Scaled<N>> = None;

        intermediate
            .into_iter()
            .zip(max_carries)
            .for_each(|(mut terms, carry_max)| {
                if let Some(carry) = carry {
                    terms.push(carry);
                }
                let carry_tmp_0: Witness<N> = stack.compose(&terms[..], N::ZERO);

                let carry_tmp_1 = &stack
                    .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
                    .0;

                stack.equal(&carry_tmp_0, carry_tmp_1);

                carry = Some(carry_tmp_0.scale(*base));
            });

        let w = integer.native().into();
        let qp = quotient * -self.rns.wrong_in_native;
        let r = result.native().sub();
        stack.zero_sum(&[w, qp, r], N::ZERO);

        result
    }

    pub fn reduce<Stack: SecondDegreeChip<N> + FirstDegreeChip<N>>(
        &self,
        stack: &mut Stack,
        integer: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let (result, quotient) = self.rns.reduction_witness(integer);

        let result = self.range(stack, result, Range::Remainder);
        let quotient = stack
            .decompose::<NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>(quotient)
            .0;

        let base = self.rns.rsh(1);
        let intermediate = integer
            .limbs()
            .iter()
            .zip(result.limbs().iter())
            .zip(self.rns.neg_wrong_limbs_in_binary.iter())
            .map(|((limb, r), w)| {
                vec![
                    quotient.scale(*w * *base),
                    limb.scale(*base),
                    r.scale(-*base),
                ]
            })
            .collect::<Vec<_>>();

        let mut carry_max = BigUint::zero();
        let max_carries = integer
            .max_vals()
            .iter()
            .take(self.rns.number_of_carries)
            .zip(self.rns.big_neg_wrong_limbs_in_binary.iter())
            .map(|(limb, w)| {
                let t = &self.rns.max_reduction_quotient * w + limb + &carry_max;
                carry_max = t >> LIMB_SIZE;
                carry_max.bits()
            });

        let mut carry: Option<Scaled<N>> = None;

        intermediate
            .into_iter()
            .zip(max_carries)
            .for_each(|(mut terms, carry_max)| {
                if let Some(carry) = carry {
                    terms.push(carry);
                }
                let carry_tmp_0: Witness<N> = stack.compose(&terms[..], N::ZERO);

                let carry_tmp_1 = &stack
                    .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
                    .0;

                stack.equal(&carry_tmp_0, carry_tmp_1);

                carry = Some(carry_tmp_0.scale(*base));
            });

        let w = integer.native().into();
        let qp = quotient * -self.rns.wrong_in_native;
        let r = result.native().sub();
        stack.zero_sum(&[w, qp, r], N::ZERO);

        result
    }

    pub fn assert_zero<Stack: SecondDegreeChip<N> + FirstDegreeChip<N>>(
        &self,
        stack: &mut Stack,
        integer: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        let (_result, quotient) = self.rns.reduction_witness(integer);
        #[cfg(feature = "prover-sanity")]
        {
            _result
                .big()
                .map(|result| assert_eq!(result, BigUint::zero()));
        }

        let quotient = stack
            .decompose::<NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>(quotient)
            .0;

        let base = self.rns.rsh(1);
        let intermediate = integer
            .limbs()
            .iter()
            .zip(self.rns.neg_wrong_limbs_in_binary.iter())
            .map(|(limb, w)| vec![quotient.scale(*w * *base), limb.scale(*base)])
            .collect::<Vec<_>>();

        let mut carry_max = BigUint::zero();
        let max_carries = integer
            .max_vals()
            .iter()
            .take(self.rns.number_of_carries)
            .zip(self.rns.big_neg_wrong_limbs_in_binary.iter())
            .map(|(limb, w)| {
                let t = &self.rns.max_reduction_quotient * w + limb + &carry_max;
                carry_max = t >> LIMB_SIZE;
                carry_max.bits()
            });

        let mut carry: Option<Scaled<N>> = None;

        intermediate
            .into_iter()
            .zip(max_carries)
            .for_each(|(mut terms, carry_max)| {
                if let Some(carry) = carry {
                    terms.push(carry);
                }
                let carry_tmp_0: Witness<N> = stack.compose(&terms[..], N::ZERO);

                let carry_tmp_1 = &stack
                    .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
                    .0;

                stack.equal(&carry_tmp_0, carry_tmp_1);

                carry = Some(carry_tmp_0.scale(*base));
            });

        let w: Scaled<N> = integer.native().into();
        let qp: Scaled<N> = quotient * -self.rns.wrong_in_native;
        stack.zero_sum(&[w, qp], N::ZERO);
    }
}
