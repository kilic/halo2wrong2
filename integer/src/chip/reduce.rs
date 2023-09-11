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
            .limbs
            .iter()
            .zip(result.limbs.iter())
            .zip(self.rns.negative_wrong_modulus_decomposed.iter())
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
            .max_vals
            .iter()
            .zip(self.rns.negative_wrong_modulus_decomposed_big.iter())
            .map(|(limb, w)| {
                let t = &self.rns.max_reduction_quotient_value * w + limb + &carry_max;
                carry_max = t >> LIMB_SIZE;
                carry_max.bits()
            });

        let mut carry: Option<Scaled<N>> = None;

        intermediate
            .into_iter()
            .zip(max_carries)
            .for_each(|(mut terms, carry_max)| {
                // let mut terms = terms
                //     .iter()
                //     .map(|terms| terms.scale(*rsh))
                //     .collect::<Vec<_>>();
                if let Some(carry) = carry {
                    terms.push(carry);
                }
                let carry_tmp_0: Witness<N> = stack.compose(&terms[..], N::ZERO).into();

                let carry_tmp_1 = &stack
                    .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
                    .0;

                stack.equal(&carry_tmp_0, carry_tmp_1);

                carry = Some(carry_tmp_0.scale(*base));
            });

        result
    }

    // pub fn assert_zero<Stack: CRT256Chip<N, NUMBER_OF_LIMBS> + FirstDegreeChip<N>>(
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
            .limbs
            .iter()
            .zip(self.rns.negative_wrong_modulus_decomposed.iter())
            .map(|(limb, w)| vec![quotient.scale(*w * *base), limb.scale(*base)])
            .collect::<Vec<_>>();

        let mut carry_max = BigUint::zero();
        let max_carries = integer
            .max_vals
            .iter()
            .zip(self.rns.negative_wrong_modulus_decomposed_big.iter())
            .map(|(limb, w)| {
                let t = &self.rns.max_reduction_quotient_value * w + limb + &carry_max;
                carry_max = t >> LIMB_SIZE;
                carry_max.bits()
            });

        let mut prev: Option<_> = None;
        let rsh = self.rns.rsh(1);

        intermediate
            .iter()
            .zip(max_carries)
            .for_each(|(terms, max_carry)| {
                let terms = terms
                    .iter()
                    .map(|terms| terms.scale(*rsh))
                    .chain(std::iter::once(prev.unwrap_or(Scaled::dummy())))
                    .collect::<Vec<_>>();
                let carry = stack.compose(&terms[..], N::ZERO).into();
                prev = Some(carry);
            });
    }

    // pub fn reduce(
    //     &self,
    //     stack: &mut CRTChip<N, NUMBER_OF_LIMBS>,
    //     integer: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    // ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
    //     let (result, quotient) = self.rns.reduction_witness(integer);

    //     let result = self.range(stack, result, Range::Remainder);
    //     let quotient = stack
    //         .decompose::<NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>(quotient)
    //         .0;
    //     let modulus = self.rns.negative_wrong_modulus_decomposed;

    //     let base = self.rns.rsh(1);
    //     let terms = integer
    //         .limbs
    //         .iter()
    //         .zip(result.limbs.iter())
    //         .zip(modulus.iter())
    //         .map(|((limb, r), w)| {
    //             vec![
    //                 quotient.scale(*w * *base),
    //                 limb.scale(*base),
    //                 r.scale(-*base),
    //             ]
    //         });

    //     let modulus = &self.rns.negative_wrong_modulus_decomposed_big;
    //     let mut carry_max = BigUint::zero();
    //     let max_carries = integer
    //         .max_vals
    //         .iter()
    //         .zip(modulus.iter())
    //         .map(|(limb, w)| {
    //             let t = &self.rns.max_reduction_quotient_value * w + limb + &carry_max;
    //             carry_max = t >> LIMB_SIZE;
    //             carry_max.bits()
    //         });

    //     let mut carry: Scaled<N> = Scaled::dummy();
    //     for (terms, carry_max) in terms.zip(max_carries) {
    //         let terms = terms
    //             .iter()
    //             .chain(std::iter::once(&carry.clone()))
    //             .cloned()
    //             .collect::<Vec<Scaled<N>>>();

    //         let carry_tmp_0 = &stack.compose(&terms[..], N::ZERO);

    //         let carry_tmp_1 = &stack
    //             .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
    //             .0;

    //         stack.equal(carry_tmp_0, carry_tmp_1);
    //         carry = carry_tmp_0.scale(*base);
    //     }

    //     let w = integer.native().into();
    //     let qp = quotient * -self.rns.wrong_modulus_in_native_modulus;
    //     let r = result.native().sub();
    //     stack.zero_sum(&[w, qp, r], N::ZERO);

    //     result
    // }

    // pub fn assert_zero(
    //     &self,
    //     stack: &mut CRTChip<N, NUMBER_OF_LIMBS>,
    //     integer: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    // ) {
    //     let (_result, quotient) = self.rns.reduction_witness(integer);
    //     #[cfg(feature = "prover-sanity")]
    //     {
    //         _result
    //             .big()
    //             .map(|result| assert_eq!(result, BigUint::zero()));
    //     }

    //     let quotient = stack
    //         .decompose::<NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>(quotient)
    //         .0;
    //     let modulus = self.rns.negative_wrong_modulus_decomposed;

    //     let base = self.rns.rsh(1);
    //     let terms = integer
    //         .limbs
    //         .iter()
    //         .zip(modulus.iter())
    //         .map(|(limb, w)| vec![quotient.scale(*w * *base), limb.scale(*base)]);

    //     let modulus = &self.rns.negative_wrong_modulus_decomposed_big;
    //     let mut carry_max = BigUint::zero();
    //     let max_carries = integer
    //         .max_vals
    //         .iter()
    //         .zip(modulus.iter())
    //         .map(|(limb, w)| {
    //             let t = &self.rns.max_reduction_quotient_value * w + limb + &carry_max;
    //             carry_max = t >> LIMB_SIZE;
    //             carry_max.bits()
    //         });

    //     let mut carry: Scaled<N> = Scaled::dummy();
    //     for (terms, carry_max) in terms.zip(max_carries) {
    //         let terms = terms
    //             .iter()
    //             .chain(std::iter::once(&carry.clone()))
    //             .cloned()
    //             .collect::<Vec<Scaled<N>>>();

    //         let carry_tmp_0 = &stack.compose(&terms[..], N::ZERO);

    //         let carry_tmp_1 = &stack
    //             .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
    //             .0;

    //         stack.equal(carry_tmp_0, carry_tmp_1);
    //         carry = carry_tmp_0.scale(*base);
    //     }

    //     let w: Scaled<N> = integer.native().into();
    //     let qp: Scaled<N> = quotient * -self.rns.wrong_modulus_in_native_modulus;
    //     stack.zero_sum(&[w, qp], N::ZERO);
    // }
}
