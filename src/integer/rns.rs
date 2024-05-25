use crate::integer::{ConstantInteger, Integer, Range, UnassignedInteger};
use crate::utils::{big_to_fe, big_to_fe_unsafe, compose_into, decompose, invert, modulus};
use ff::PrimeField;
use halo2::circuit::Value;
use num_bigint::BigUint;
use num_integer::{div_ceil, Integer as _};
use num_traits::{One, Zero};
use std::marker::PhantomData;

use super::schoolbook;

#[derive(Debug, Clone)]
pub struct Rns<W: PrimeField, N: PrimeField> {
    pub number_of_limbs: usize,
    pub limb_size: usize,

    pub(crate) wrong_modulus: BigUint,
    pub(crate) native_modulus: BigUint,

    pub(super) left_shifters: Vec<N>,
    pub(super) right_shifters: Vec<N>,

    pub(super) big_neg_wrong_limbs_in_binary: Vec<BigUint>,
    pub(super) neg_wrong_limbs_in_binary: Vec<N>,
    pub(super) wrong_limbs: Vec<N>,
    pub(super) big_wrong_limbs: Vec<BigUint>,

    pub(super) wrong_in_native: N,

    pub(super) _max_limb: BigUint,
    pub(super) max_reduction_quotient: BigUint,
    pub(super) max_remainder: BigUint,
    pub(super) max_operand: BigUint,
    pub(super) max_quotient: BigUint,
    pub(super) max_remainder_limbs: Vec<BigUint>,
    pub(super) max_operand_limbs: Vec<BigUint>,
    pub(super) max_quotient_limbs: Vec<BigUint>,

    pub(super) number_of_carries: usize,

    pub max_most_significant_limb_size: usize,

    pub(super) _max_unreduced_limb: BigUint,
    pub(super) _max_unreduced_value: BigUint,

    _marker: PhantomData<W>,
}

impl<W: PrimeField, N: PrimeField> Rns<W, N> {
    pub fn decompose(&self, e: &BigUint) -> Vec<BigUint> {
        decompose(e, self.number_of_limbs, self.limb_size)
    }

    pub fn unassigned(&self, e: Value<W>) -> UnassignedInteger<W, N> {
        UnassignedInteger::<W, N>::from_fe(e, self.number_of_limbs, self.limb_size)
    }

    pub fn constant(&self, e: &W) -> ConstantInteger<W, N> {
        ConstantInteger::<W, N>::from_fe(e, self.number_of_limbs, self.limb_size)
    }

    pub(crate) fn shift_sub_aux(
        &self,
        base_sub_aux: &[BigUint],
        shift: usize,
    ) -> (Vec<N>, Vec<BigUint>, N) {
        let aux_big = base_sub_aux
            .iter()
            .map(|aux_limb| aux_limb << shift)
            .collect::<Vec<_>>();
        let aux = aux_big.iter().map(|e| big_to_fe(e)).collect::<Vec<N>>();
        let native = compose_into::<N, N>(&aux, self.limb_size);
        (aux, aux_big, native)
    }

    pub fn construct(limb_size: usize) -> Self {
        let one = &BigUint::one();

        macro_rules! log_floor {
            ($u:expr) => {
                &(one << ($u.bits() as usize - 1))
            };
        }

        // wrong field modulus: `w`
        let wrong_modulus = &modulus::<W>();
        // native field modulus: `n`
        let native_modulus = &modulus::<N>();

        // `op * op < q * w + r < bin * p`
        // `CRT = bin * nat`

        // `p` native modulus, `w` wrong modulus and `r` max remainder are known
        // `op` max operand  (some power of two minus one)
        // `q`  max quotient (some power of two minus one)
        // `bin` binary modulus to satisfy CRT where `CRT = bin * nat`

        // 1. estimate `bin`
        // 2. find `q`
        // 3. find `op`
        // 4. if `q` or `op` is shy against `w`e increase `bin` once and try again

        println!("w: {}", wrong_modulus.bits());
        let number_of_limbs = div_ceil(wrong_modulus.bits() as usize, limb_size);
        let max_limb = (one << limb_size) - 1usize;

        // assert that number of limbs is set correctly
        assert_eq!(
            number_of_limbs,
            div_ceil(wrong_modulus.bits() as usize, limb_size)
        );

        // Max remainder is next power of two of wrong modulus.
        // Witness remainder might overflow the wrong modulus but it is limited
        // to the next power of two of the wrong modulus.
        let max_remainder = (one << wrong_modulus.bits()) - 1usize;

        // with a conservative margin we start with max operand is equal to max remainder approximation
        let pre_binary_modulus = max_remainder.pow(2) / native_modulus;
        let pre_binary_modulus_size = pre_binary_modulus.bits() as usize;
        let mut number_of_carries = div_ceil(pre_binary_modulus_size, limb_size);

        println!(
            "RNS construction, limb_size: {limb_size}, number_of_limbs: {number_of_limbs}, number_of_carries {number_of_carries}"
        );

        // rounding down max quotient and max operand to `2^k - 1` for cheaper range checks
        // may result in a smaller binary modulus so we need to refine number of carries and
        // binary modulus size
        let (number_of_carries, binary_modulus, crt_modulus, max_quotient, max_operand) = (0..2)
            .find_map(|_| {
                let binary_modulus_size = number_of_carries * limb_size;
                let binary_modulus = one << binary_modulus_size;
                let crt_modulus = &binary_modulus * native_modulus;

                // find max quotient
                // first value is not power of two minus one
                let pre_max_quotient = (&crt_modulus - &max_remainder) / wrong_modulus;
                // so lets floor it to there
                let mut max_quotient = (one << (pre_max_quotient.bits() - 1)) - 1usize;

                let number_of_quotient_limbs = div_ceil(max_quotient.bits() as usize, limb_size);
                if number_of_quotient_limbs > number_of_limbs {
                    max_quotient = (one << (number_of_limbs * limb_size)) - 1usize;
                }

                // `op * op < q * w + r`
                let tt = &max_quotient * wrong_modulus + &max_remainder;
                let pre_max_operand = tt.sqrt();
                let max_operand = log_floor!(pre_max_operand) - 1usize;

                if &max_quotient < wrong_modulus {
                    println!("q < w; go second try");
                    number_of_carries += 1;
                    return None;
                }
                if &max_operand < wrong_modulus {
                    println!("op < w; go second try");
                    number_of_carries += 1;
                    return None;
                }

                Some((
                    number_of_carries,
                    binary_modulus,
                    crt_modulus,
                    max_quotient,
                    max_operand,
                ))
            })
            .unwrap();

        {
            let lhs = &max_operand * &max_operand;
            let rhs = &max_quotient * wrong_modulus + &max_remainder;
            assert!(&binary_modulus > wrong_modulus);
            assert!(&binary_modulus > native_modulus);
            assert!(&max_remainder > wrong_modulus);

            assert!(rhs < crt_modulus);
            assert!(lhs < rhs);

            assert!(&max_quotient > wrong_modulus);
            assert!(&max_operand > wrong_modulus);

            assert!(max_remainder < binary_modulus);
            assert!(max_operand < binary_modulus);
            assert!(max_quotient < binary_modulus);
        }

        let max_most_significant_limb = &max_remainder >> ((number_of_limbs - 1) * limb_size);
        let max_most_significant_limb_size = max_most_significant_limb.bits() as usize;
        let max_remainder_limbs = std::iter::repeat_with(|| max_limb.clone())
            .take(number_of_limbs - 1)
            .chain(std::iter::once(max_most_significant_limb))
            .collect::<Vec<_>>();

        let max_most_significant_limb = &max_quotient >> ((number_of_limbs - 1) * limb_size);
        let max_quotient_limbs = std::iter::repeat_with(|| max_limb.clone())
            .take(number_of_limbs - 1)
            .chain(std::iter::once(max_most_significant_limb))
            .collect::<Vec<_>>();

        let max_most_significant_limb = &max_operand >> ((number_of_limbs - 1) * limb_size);
        let max_operand_limbs = std::iter::repeat_with(|| max_limb.clone())
            .take(number_of_limbs - 1)
            .chain(std::iter::once(max_most_significant_limb))
            .collect::<Vec<_>>();

        let max_reduction_quotient = (one << limb_size) - one;
        let max_unreduced_value = wrong_modulus * max_reduction_quotient.clone();
        // 1.5x of the max reduced limb
        let max_unreduced_limb = &(one << (limb_size + limb_size / 2)) - one;

        // negative wrong field modulus moduli binary modulus `w'`
        // `w' = (T - w)`
        // `w' = [w'_0, w'_1, ... ]`
        let big_neg_wrong_in_binary = binary_modulus - wrong_modulus;
        let big_neg_wrong_limbs_in_binary =
            decompose(&big_neg_wrong_in_binary, number_of_carries, limb_size);

        let neg_wrong_limbs_in_binary: Vec<_> = big_neg_wrong_limbs_in_binary
            .iter()
            .map(big_to_fe_unsafe)
            .collect::<Vec<_>>();

        let big_wrong_limbs = decompose(wrong_modulus, number_of_limbs, limb_size);
        let wrong_limbs: Vec<_> = big_wrong_limbs.iter().map(big_to_fe).collect::<Vec<N>>();
        // `w-1 = [w_0-1 , w_1, ... ] `

        let wrong_in_native: N = big_to_fe(&(wrong_modulus % native_modulus));

        // Calculate shifter elements
        let two = N::from(2);
        // Left shifts field element by `u * limb_size` bits
        let left_shifters: Vec<_> = (0..number_of_limbs)
            .map(|i| two.pow([(i * limb_size) as u64, 0, 0, 0]))
            .collect::<Vec<N>>();
        let right_shifters: Vec<_> = left_shifters
            .iter()
            .map(|e| e.invert().unwrap())
            .collect::<Vec<_>>();

        Self {
            number_of_limbs,
            limb_size,

            left_shifters,
            right_shifters,
            wrong_modulus: wrong_modulus.clone(),
            native_modulus: native_modulus.clone(),
            max_reduction_quotient,
            neg_wrong_limbs_in_binary,
            big_neg_wrong_limbs_in_binary,
            wrong_limbs,
            big_wrong_limbs,
            wrong_in_native,
            max_remainder: max_remainder.clone(),
            max_operand: max_operand.clone(),
            max_quotient: max_quotient.clone(),
            max_quotient_limbs,
            max_remainder_limbs,
            max_operand_limbs,
            _max_limb: max_limb,
            number_of_carries,

            max_most_significant_limb_size,

            _max_unreduced_limb: max_unreduced_limb,
            _max_unreduced_value: max_unreduced_value,

            _marker: PhantomData,
        }
    }

    pub(crate) fn rsh(&self, i: usize) -> &N {
        &self.right_shifters[i]
    }

    pub fn max_values(&self, range: Range) -> Vec<BigUint> {
        match range {
            Range::Remainder => self.max_remainder_limbs.clone(),
            Range::Operand => self.max_operand_limbs.clone(),
            Range::Unreduced => std::iter::repeat_with(|| self._max_unreduced_limb.clone())
                .take(self.number_of_limbs)
                .collect::<Vec<_>>(),
            Range::MulQuotient => self.max_quotient_limbs.clone(),
        }
    }

    pub(crate) fn reduction_witness(
        &self,
        w: &Integer<W, N>,
    ) -> (UnassignedInteger<W, N>, Value<N>) {
        let (quotient, result) = w.big().map(|w| w.div_rem(&self.wrong_modulus)).unzip();

        #[cfg(feature = "prover-sanity")]
        {
            quotient
                .as_ref()
                .map(|quotient| assert!(quotient < &self.max_reduction_quotient));
        }
        let quotient = quotient.map(|quotient| big_to_fe_unsafe(&quotient));
        let result =
            UnassignedInteger::<W, N>::from_big(result, self.number_of_limbs, self.limb_size);

        (result, quotient)
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn mul_witness(
        &self,
        w0: &Integer<W, N>,
        w1: &Integer<W, N>,
        to_add: &[&Integer<W, N>],
    ) -> (UnassignedInteger<W, N>, UnassignedInteger<W, N>) {
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

        let quotient =
            UnassignedInteger::<W, N>::from_big(quotient, self.number_of_limbs, self.limb_size);
        let result =
            UnassignedInteger::<W, N>::from_big(result, self.number_of_limbs, self.limb_size);

        (result, quotient)
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn mul_witness_constant(
        &self,
        w0: &Integer<W, N>,
        w1: &ConstantInteger<W, N>,
        to_add: &[&Integer<W, N>],
    ) -> (UnassignedInteger<W, N>, UnassignedInteger<W, N>) {
        let to_add = to_add.iter().map(|e| e.big());
        let to_add: Value<Vec<_>> = Value::from_iter(to_add);
        let (quotient, result) = w0
            .big()
            .zip(to_add)
            .map(|(w0, to_add)| {
                let to_add = to_add.iter().sum::<BigUint>();
                (w0 * w1.big() + to_add).div_rem(&self.wrong_modulus)
            })
            .unzip();

        #[cfg(feature = "prover-sanity")]
        {
            quotient
                .as_ref()
                .map(|quotient| assert!(quotient < &self.max_quotient));
        }

        let quotient =
            UnassignedInteger::<W, N>::from_big(quotient, self.number_of_limbs, self.limb_size);
        let result =
            UnassignedInteger::<W, N>::from_big(result, self.number_of_limbs, self.limb_size);

        (result, quotient)
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn neg_mul_add_div_witness(
        &self,
        w0: &Integer<W, N>,
        w1: &Integer<W, N>,
        denom: &Integer<W, N>,
        to_add: &[&Integer<W, N>],
    ) -> (UnassignedInteger<W, N>, UnassignedInteger<W, N>) {
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

        let quotient =
            UnassignedInteger::<W, N>::from_big(quotient, self.number_of_limbs, self.limb_size);
        let result =
            UnassignedInteger::<W, N>::from_big(result, self.number_of_limbs, self.limb_size);

        (result, quotient)
    }

    pub(crate) fn inv_witness(
        &self,
        denom: &Integer<W, N>,
    ) -> (UnassignedInteger<W, N>, UnassignedInteger<W, N>) {
        let (result, quotient) = denom
            .big()
            .map(|denom| {
                let denom_inv = invert::<W>(&denom);
                let result = &denom_inv % &self.wrong_modulus;
                let (quotient, must_be_one) = (&denom * &result).div_rem(&self.wrong_modulus);
                assert_eq!(must_be_one, BigUint::one());

                (result, quotient)
            })
            .unzip();

        #[cfg(feature = "synth-sanity")]
        {
            let result_max = &self.max_remainder;
            let max_lhs = result_max * denom.max();
            let max_rhs = &self.max_quotient * &self.wrong_modulus;
            assert!(max_rhs > max_lhs);
        }

        #[cfg(feature = "prover-sanity")]
        {
            quotient
                .as_ref()
                .map(|quotient| assert!(quotient < &self.max_quotient));
        }

        let quotient =
            UnassignedInteger::<W, N>::from_big(quotient, self.number_of_limbs, self.limb_size);
        let result =
            UnassignedInteger::<W, N>::from_big(result, self.number_of_limbs, self.limb_size);

        (result, quotient)
    }

    pub(crate) fn div_witness(
        &self,
        numer: &Integer<W, N>,
        denom: &Integer<W, N>,
    ) -> (
        UnassignedInteger<W, N>,
        UnassignedInteger<W, N>,
        ConstantInteger<W, N>,
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
            let result_max = &self.max_remainder;
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

        let quotient =
            UnassignedInteger::<W, N>::from_big(quotient, self.number_of_limbs, self.limb_size);
        let result =
            UnassignedInteger::<W, N>::from_big(result, self.number_of_limbs, self.limb_size);
        let shifter =
            ConstantInteger::<W, N>::from_big(shifter, self.number_of_limbs, self.limb_size);

        (result, quotient, shifter)
    }

    pub(crate) fn mul_max_carries(
        &self,
        w0: &[BigUint],
        w1: &[BigUint],
        to_add: &[&[BigUint]],
    ) -> Vec<usize> {
        let mut carry_max = BigUint::zero();
        let ww = schoolbook::<BigUint, BigUint, BigUint>(w0, w1);
        let pq = schoolbook::<BigUint, BigUint, BigUint>(
            &self.max_quotient_limbs,
            &self.big_neg_wrong_limbs_in_binary,
        ); // TODO: precompute

        let to_add = (0..self.number_of_limbs).map(|i| {
            to_add
                .iter()
                .map(|e| e[i].clone())
                .chain(std::iter::repeat(BigUint::zero()))
                .take(self.number_of_carries)
                .collect::<Vec<_>>()
        });

        ww.iter()
            .zip(pq)
            .zip(to_add)
            .take(self.number_of_carries)
            .map(|((ww, pq), to_add)| {
                let t = ww
                    .iter()
                    .chain(pq.iter())
                    .chain(to_add.iter())
                    .chain(std::iter::once(&carry_max))
                    .sum::<BigUint>();
                assert!(t < self.native_modulus, "wraps");
                carry_max = t >> self.limb_size;
                carry_max.bits() as usize
            })
            .collect()
    }

    pub(crate) fn neg_mul_div_max_carries(
        &self,
        w0: &[BigUint],
        w1: &[BigUint],
        divisor: &[BigUint],
        to_add: &[&[BigUint]],
    ) -> Vec<usize> {
        let mut carry_max = BigUint::zero();
        let ww = schoolbook::<BigUint, BigUint, BigUint>(w0, w1);
        let pq = schoolbook::<BigUint, BigUint, BigUint>(
            &self.max_quotient_limbs,
            &self.big_neg_wrong_limbs_in_binary,
        ); // TODO: precompute
        let rd = schoolbook::<BigUint, BigUint, BigUint>(&self.max_remainder_limbs, divisor);

        let to_add = (0..self.number_of_limbs).map(|i| {
            to_add
                .iter()
                .map(|e| e[i].clone())
                .chain(std::iter::repeat(BigUint::zero()))
                .take(self.number_of_carries)
                .collect::<Vec<_>>()
        });

        ww.iter()
            .zip(rd)
            .zip(pq)
            .zip(to_add)
            .take(self.number_of_carries)
            .map(|(((ww, rd), pq), to_add)| {
                let t = ww
                    .iter()
                    .chain(rd.iter())
                    .chain(pq.iter())
                    .chain(to_add.iter())
                    .chain(std::iter::once(&carry_max))
                    .sum::<BigUint>();
                assert!(t < self.native_modulus, "wraps");
                carry_max = t >> self.limb_size;
                carry_max.bits() as usize
            })
            .collect()
    }
}
