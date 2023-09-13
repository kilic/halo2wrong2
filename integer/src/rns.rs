use crate::integer::{ConstantInteger, Integer, Range, UnassignedInteger};
use circuitry::utils::{
    big_to_fe, big_to_fe_unsafe, compose, decompose, fe_to_big, invert, modulus,
};
use ff::PrimeField;
use halo2::circuit::Value;
use num_bigint::BigUint;
use num_integer::Integer as _;
use num_traits::{One, Zero};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
pub struct Rns<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize> {
    pub(crate) wrong_modulus: BigUint,
    pub(crate) native_modulus: BigUint,
    pub(super) left_shifters: [N; NUMBER_OF_LIMBS],
    pub(super) right_shifters: [N; NUMBER_OF_LIMBS],

    pub(super) base_aux: [BigUint; NUMBER_OF_LIMBS],

    pub(super) negative_wrong_modulus_decomposed_big: [BigUint; NUMBER_OF_LIMBS],
    pub(super) negative_wrong_modulus_decomposed: [N; NUMBER_OF_LIMBS],
    pub(super) wrong_modulus_limbs: [N; NUMBER_OF_LIMBS],

    pub(super) wrong_modulus_in_native_modulus: N,
    pub(super) _max_reduced_limb: BigUint,

    pub(super) max_reduction_quotient_value: BigUint,
    pub(super) max_unreduced_value: BigUint,

    pub(super) _max_remainder: BigUint,
    pub(super) max_operand: BigUint,
    pub(super) max_quotient: BigUint,
    pub(super) max_most_significant_reduced_limb: BigUint,
    pub(super) max_most_significant_operand_limb: BigUint,
    pub(super) max_most_significant_mul_quotient_limb: BigUint,

    // unreduced_zero: BigUint,
    // unreduced_zero_decomposed: [N; NUMBER_OF_LIMBS],
    #[cfg(test)]
    pub(super) max_unreduced_limb: BigUint,
    _marker: PhantomData<W>,
}

impl<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>
    Rns<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>
{
    fn calculate_base_aux() -> [BigUint; NUMBER_OF_LIMBS] {
        let two = N::from(2);
        let r = &fe_to_big(&two.pow([LIMB_SIZE as u64, 0, 0, 0]));
        let wrong_modulus = modulus::<W>();
        let wrong_modulus_limbs_big = decompose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&wrong_modulus);
        let wrong_modulus_limbs: [N; NUMBER_OF_LIMBS] = wrong_modulus_limbs_big
            .iter()
            .map(|limb| big_to_fe_unsafe(limb))
            .collect::<Vec<N>>()
            .try_into()
            .unwrap();

        // `base_aux = 2 * wrong_modulus`
        let mut base_aux: Vec<BigUint> = wrong_modulus_limbs
            .iter()
            .map(|limb| fe_to_big(limb) << 1usize)
            .collect();

        // If value of a limb is not above dense limb borrow from the next one
        for i in 0..NUMBER_OF_LIMBS - 1 {
            let hidx = NUMBER_OF_LIMBS - i - 1;
            let lidx = hidx - 1;

            if (base_aux[lidx].bits() as usize) < (LIMB_SIZE + 1) {
                base_aux[hidx] = base_aux[hidx].clone() - 1usize;
                base_aux[lidx] = base_aux[lidx].clone() + r;
            }
        }

        base_aux.try_into().unwrap()
    }

    pub fn construct() -> Self {
        assert!(NUMBER_OF_LIMBS > 2);
        let one = &BigUint::one();
        // previous power of two
        macro_rules! log_floor {
            ($u:expr) => {
                &(one << ($u.bits() as usize - 1))
            };
        }
        // next power of two
        macro_rules! log_ceil {
            ($u:expr) => {
                &(one << $u.bits() as usize)
            };
        }
        // `t = LIMB_SIZE * NUMBER_OF_LIMBS`
        // `T = 2 ^ t` which we also name as `binary_modulus`
        let binary_modulus_bit_len = LIMB_SIZE * NUMBER_OF_LIMBS;
        let binary_modulus = &(one << binary_modulus_bit_len);
        // wrong field modulus: `w`
        let wrong_modulus = &modulus::<W>();
        // native field modulus: `n`
        let native_modulus = &modulus::<N>();

        let wrong_modulus_limbs_big = decompose::<NUMBER_OF_LIMBS, LIMB_SIZE>(wrong_modulus);
        let wrong_modulus_limbs: [N; NUMBER_OF_LIMBS] = wrong_modulus_limbs_big
            .iter()
            .map(|limb| big_to_fe(limb))
            .collect::<Vec<N>>()
            .try_into()
            .unwrap();

        // Multiplication is constrained as:
        //
        // `a * b = w * quotient + remainder`
        //
        // where `quotient` and `remainder` is witnesses, `a` and `b` are assigned
        // operands. Both sides of the equation must not wrap `crt_modulus`.
        let crt_modulus = &(binary_modulus * native_modulus);

        // Witness remainder might overflow the wrong modulus but it is limited
        // to the next power of two of the wrong modulus.
        let max_remainder = &(log_ceil!(wrong_modulus) - one);

        // Find maxium quotient that won't wrap `quotient * wrong + remainder` side of
        // the equation under `crt_modulus`.
        let pre_max_quotient: &BigUint = &((crt_modulus - max_remainder) / wrong_modulus);
        // Lower this value to make this value suitable for bit range checks.
        let max_quotient = &(log_floor!(pre_max_quotient) - one);

        // Find the maximum operand: in order to meet completeness maximum allowed
        // operand value is saturated as below:
        //
        // `max_operand ^ 2 < max_quotient * wrong + max_remainder`
        //
        // So that prover can find `quotient` and `remainder` witnesses for any
        // allowed input operands. And it also automativally ensures that:
        //
        // `max_operand^2 < crt_modulus`
        //
        // must hold.
        let max_operand_bit_len = ((max_quotient * wrong_modulus + max_remainder).bits() - 1) / 2;
        let max_operand = &((one << max_operand_bit_len) - one);
        // Sanity check
        {
            let lhs = &(max_operand * max_operand);
            let rhs = &(max_quotient * wrong_modulus + max_remainder);
            assert!(binary_modulus > wrong_modulus);
            assert!(binary_modulus > native_modulus);
            assert!(max_remainder > wrong_modulus);
            assert!(max_operand > wrong_modulus);
            assert!(max_quotient > wrong_modulus);
            assert!(max_remainder < binary_modulus);
            assert!(max_operand < binary_modulus);
            assert!(max_quotient < binary_modulus);
            assert!(rhs < crt_modulus);
            assert!(lhs < rhs);
        }
        // negative wrong field modulus moduli binary modulus `w'`
        // `w' = (T - w)`
        // `w' = [w'_0, w'_1, ... ]`
        let negative_wrong_modulus_decomposed_big =
            decompose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&(binary_modulus - wrong_modulus));

        // Full dense limb without overflow
        let max_reduced_limb = &(one << LIMB_SIZE) - one;

        // Most significant limbs are subjected to different range checks which will be
        // probably less than full sized limbs.
        let max_most_significant_reduced_limb =
            &(max_remainder >> ((NUMBER_OF_LIMBS - 1) * LIMB_SIZE));
        let max_most_significant_operand_limb =
            &(max_operand >> ((NUMBER_OF_LIMBS - 1) * LIMB_SIZE));
        let max_most_significant_mul_quotient_limb =
            &(max_quotient >> ((NUMBER_OF_LIMBS - 1) * LIMB_SIZE));

        // Calculate auxillary value for subtraction
        let base_aux = Self::calculate_base_aux();
        // Sanity check for auxillary value
        {
            let base_aux_value = compose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&base_aux);
            // Must be equal to wrong modulus
            assert!(base_aux_value.clone() % wrong_modulus == BigUint::zero());
            // Expected to be above next power of two
            assert!(base_aux_value > *max_remainder);
            // Assert limbs are above max values
            for (i, aux) in base_aux.iter().enumerate() {
                let is_last_limb = i == NUMBER_OF_LIMBS - 1;
                let target = if is_last_limb {
                    max_most_significant_reduced_limb.clone()
                } else {
                    max_reduced_limb.clone()
                };
                assert!(*aux >= target);
            }
        }

        let wrong_modulus_in_native_modulus: N = big_to_fe(&(wrong_modulus % native_modulus));

        // Calculate shifter elements
        let two = N::from(2);
        // Left shifts field element by `u * LIMB_SIZE` bits
        let left_shifters: [N; NUMBER_OF_LIMBS] = (0..NUMBER_OF_LIMBS)
            .map(|i| two.pow([(i * LIMB_SIZE) as u64, 0, 0, 0]))
            .collect::<Vec<N>>()
            .try_into()
            .unwrap();

        let negative_wrong_modulus_decomposed: [N; NUMBER_OF_LIMBS] =
            negative_wrong_modulus_decomposed_big
                .iter()
                .map(big_to_fe_unsafe)
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();

        let right_shifters = left_shifters
            .iter()
            .map(|e| e.invert().unwrap())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let max_reduction_quotient_value = (one << LIMB_SIZE) - one;
        let max_unreduced_value = wrong_modulus * max_reduction_quotient_value.clone();
        // let should_reduce_after = (wrong_modulus - 1usize) * max_reduction_quotient_value;

        Self {
            left_shifters,
            right_shifters,
            wrong_modulus: wrong_modulus.clone(),
            native_modulus: native_modulus.clone(),
            base_aux,
            negative_wrong_modulus_decomposed,
            negative_wrong_modulus_decomposed_big,
            // wrong_modulus_limbs_big,
            wrong_modulus_limbs,
            wrong_modulus_in_native_modulus,
            _max_reduced_limb: max_reduced_limb,
            #[cfg(test)]
            max_unreduced_limb: &(one << (LIMB_SIZE + LIMB_SIZE / 2)) - one,

            max_reduction_quotient_value,
            max_unreduced_value,

            _max_remainder: max_remainder.clone(),
            max_operand: max_operand.clone(),
            max_quotient: max_quotient.clone(),
            max_most_significant_reduced_limb: max_most_significant_reduced_limb.clone(),
            max_most_significant_operand_limb: max_most_significant_operand_limb.clone(),
            max_most_significant_mul_quotient_limb: max_most_significant_mul_quotient_limb.clone(),

            _marker: PhantomData,
        }
        // Another sanity check for maximum reducible value:
        // TODO: uncomment
        // {
        //     let max_with_max_unreduced_limbs = &[big_to_fe(max_unreduced_limb); NUMBER_OF_LIMBS];
        //     let max_with_max_unreduced =
        //         Integer::from_limbs(max_with_max_unreduced_limbs, Rc::new(rns.clone()));
        //     let reduction_result = max_with_max_unreduced.reduction_witness();
        //     let quotient = match reduction_result.quotient {
        //         Quotient::Short(quotient) => quotient,
        //         _ => panic!("short quotient is expected"),
        //     };
        //     let quotient = fe_to_big(quotient);
        //     assert!(quotient < max_reduced_limb);
        // }

        // rns
    }

    pub(crate) fn rsh(&self, i: usize) -> &N {
        &self.right_shifters[i]
    }

    pub(crate) fn last_limb_max(&self, range: Range) -> (BigUint, usize) {
        let bit_len = match range {
            Range::Remainder => self.max_most_significant_reduced_limb.bits(),
            Range::Operand => self.max_most_significant_operand_limb.bits(),
            Range::MulQuotient => self.max_most_significant_mul_quotient_limb.bits(),
            #[cfg(test)]
            Range::Unreduced => self.max_unreduced_limb.bits(),
        } as usize;
        let max = (BigUint::one() << bit_len) - 1usize;
        (max, bit_len)
    }

    pub fn max_values(&self, range: Range) -> [BigUint; NUMBER_OF_LIMBS] {
        let max = (BigUint::one() << LIMB_SIZE) - 1usize;
        let mut max_values = vec![max; NUMBER_OF_LIMBS - 1];
        max_values.push(self.last_limb_max(range).0);
        max_values.try_into().unwrap()
    }

    pub(crate) fn reduction_witness(
        &self,
        w: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> (
        UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        Value<N>,
    ) {
        let (quotient, result) = w.big().map(|w| w.div_rem(&self.wrong_modulus)).unzip();

        #[cfg(feature = "prover-sanity")]
        {
            quotient
                .as_ref()
                .map(|quotient| assert!(quotient < &self.max_reduction_quotient_value));
        }
        let quotient = quotient.map(|quotient| big_to_fe_unsafe(&quotient));
        (result.into(), quotient)
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn mul_witness(
        &self,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        to_add: &[Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>],
    ) -> (
        UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        let to_add = to_add.iter().map(|e| e.big());
        let to_add: Value<Vec<_>> = Value::from_iter(to_add);
        let (quotient, result) = w0
            .big()
            .zip(w1.big())
            .zip(to_add)
            .map(|((w0, w1), to_add)| {
                let to_add = to_add.iter().sum::<BigUint>();
                (w0 * w1 + to_add).div_rem(&self.wrong_modulus)
            })
            .unzip();

        #[cfg(feature = "prover-sanity")]
        {
            quotient
                .as_ref()
                .map(|quotient| assert!(quotient < &self.max_quotient));
        }

        (result.into(), quotient.into())
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn neg_mul_add_div_witness(
        &self,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        denom: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        to_add: &[Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>],
    ) -> (
        UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        let to_add = to_add.iter().map(|e| e.big());
        let to_add: Value<Vec<_>> = Value::from_iter(to_add);
        let (result, quotient) = w0
            .big()
            .zip(w1.big())
            .zip(denom.big())
            .zip(to_add)
            .map(|(((w0, w1), denom), to_add)| {
                let numer = w0 * w1 + to_add.iter().sum::<BigUint>();
                let denom_inv = invert::<W>(&denom);
                let result = (&numer * &denom_inv) % &self.wrong_modulus;
                let result = &self.wrong_modulus - &result;
                let (quotient, _must_be_zero) =
                    (numer + &result * &denom).div_rem(&self.wrong_modulus);
                assert_eq!(_must_be_zero, BigUint::zero());

                (result, quotient)
            })
            .unzip();

        #[cfg(feature = "prover-sanity")]
        {
            quotient
                .as_ref()
                .map(|quotient| assert!(quotient < &self.max_quotient));
        }

        (result.into(), quotient.into())
    }

    pub(crate) fn div_witness(
        &self,
        numer: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        denom: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> (
        UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        ConstantInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        let numer_max = numer.max();
        let k = numer_max / &self.wrong_modulus;
        let shifter = k * &self.wrong_modulus;

        let (result, quotient) = numer
            .big()
            .zip(denom.big())
            .map(|(numer, denom)| {
                let denom_inv = invert::<W>(&denom);
                let result = (&denom_inv * &numer) % &self.wrong_modulus;
                let (quotient, _must_be_zero) =
                    (&denom * &result + &shifter - &numer).div_rem(&self.wrong_modulus);
                assert_eq!(_must_be_zero, BigUint::zero());

                (result, quotient)
            })
            .unzip();

        #[cfg(feature = "synth-sanity")]
        {
            let result_max = &self._max_remainder;
            let max_lhs = result_max * denom.max() + &shifter;
            let max_rhs = &self.max_quotient * &self.wrong_modulus;
            assert!(max_rhs > max_lhs);
        }

        #[cfg(feature = "prover-sanity")]
        {
            quotient
                .as_ref()
                .map(|quotient| assert!(quotient < &self.max_quotient));
        }

        (result.into(), quotient.into(), shifter.into())
    }

    // #[allow(clippy::type_complexity)]
    // pub(crate) fn mul_sub_witness(
    //     &self,
    //     w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    //     w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    //     to_sub: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    // ) -> (
    //     UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    //     UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    // ) {
    //     let (quotient, result) = w0
    //         .big()
    //         .zip(w1.big())
    //         .zip(to_sub.big())
    //         .map(|((w0, w1), to_sub)| (w0 * w1 - to_sub).div_rem(&self.wrong_modulus))
    //         // TODO/FIX : underflow bug
    //         .unzip();

    //     #[cfg(feature = "prover-sanity")]
    //     {
    //         quotient
    //             .as_ref()
    //             .map(|quotient| assert!(quotient < &self.max_quotient));
    //     }

    //     (
    //         UnassignedInteger::from(result),
    //         UnassignedInteger::from(quotient),
    //     )
    // }
}
