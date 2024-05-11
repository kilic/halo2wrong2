use crate::circuitry::chip::first_degree::FirstDegreeChip;
use crate::circuitry::chip::range::RangeChip;
use crate::circuitry::chip::Core;
use crate::circuitry::stack::Stack;
use crate::circuitry::witness::{Composable, Scaled, Witness};
use crate::integer::chip::IntegerChip;
use crate::integer::{Integer, Range};
use ff::PrimeField;
use num_bigint::BigUint;
use num_traits::Zero;

impl<W: PrimeField, N: PrimeField + Ord> IntegerChip<W, N> {
    pub fn reduce_if_necessary(
        &self,
        stack: &mut Stack<N>,
        integer: &Integer<W, N>,
    ) -> Integer<W, N> {
        if self.is_gt_max_operand(integer) {
            self.reduce(stack, integer)
        } else {
            integer.clone()
        }
    }

    pub fn reduce(&self, stack: &mut Stack<N>, integer: &Integer<W, N>) -> Integer<W, N> {
        let (result, quotient) = self.rns.reduction_witness(integer);

        let result = self.range(stack, &result, Range::Remainder);
        let quotient = stack
            .decompose(quotient, self.rns.limb_size, self.sublimb_size)
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
                carry_max = t >> self.rns.limb_size;
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
                    .decompose(carry_tmp_0.value(), carry_max as usize, self.sublimb_size)
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

    pub fn assert_zero(&self, stack: &mut Stack<N>, integer: &Integer<W, N>) {
        let (_result, quotient) = self.rns.reduction_witness(integer);
        #[cfg(feature = "prover-sanity")]
        {
            _result
                .big()
                .map(|result| assert_eq!(result, BigUint::zero()));
        }

        let quotient = stack
            .decompose(quotient, self.rns.limb_size, self.sublimb_size)
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
                carry_max = t >> self.rns.limb_size;
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
                    .decompose(carry_tmp_0.value(), carry_max as usize, self.sublimb_size)
                    .0;

                stack.equal(&carry_tmp_0, carry_tmp_1);

                carry = Some(carry_tmp_0.scale(*base));
            });

        let w: Scaled<N> = integer.native().into();
        let qp: Scaled<N> = quotient * -self.rns.wrong_in_native;
        stack.zero_sum(&[w, qp], N::ZERO);
    }
}
