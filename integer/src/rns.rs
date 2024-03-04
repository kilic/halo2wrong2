use crate::{
    integer::{ConstantInteger, Integer, Range, UnassignedInteger},
    schoolbook,
};
use circuitry::utils::{big_to_fe, big_to_fe_unsafe, decompose, invert, modulus};
use ff::PrimeField;
use halo2::circuit::Value;
use num_bigint::BigUint;
use num_integer::{div_ceil, Integer as _};
use num_traits::{One, Zero};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
pub struct Rns<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize> {
    pub(crate) wrong_modulus: BigUint,
    pub(crate) native_modulus: BigUint,

    pub(super) left_shifters: [N; NUMBER_OF_LIMBS],
    pub(super) right_shifters: [N; NUMBER_OF_LIMBS],

    pub(super) big_neg_wrong_limbs_in_binary: [BigUint; NUMBER_OF_LIMBS],
    pub(super) neg_wrong_limbs_in_binary: [N; NUMBER_OF_LIMBS],
    pub(super) wrong_limbs: [N; NUMBER_OF_LIMBS],
    pub(super) big_wrong_limbs: [BigUint; NUMBER_OF_LIMBS],

    pub(super) wrong_in_native: N,

    pub(super) _max_limb: BigUint,
    pub(super) max_reduction_quotient: BigUint,
    pub(super) max_remainder: BigUint,
    pub(super) max_operand: BigUint,
    pub(super) max_quotient: BigUint,
    pub(super) max_remainder_limbs: [BigUint; NUMBER_OF_LIMBS],
    pub(super) max_operand_limbs: [BigUint; NUMBER_OF_LIMBS],
    pub(super) max_quotient_limbs: [BigUint; NUMBER_OF_LIMBS],

    pub(super) number_of_carries: usize,

    pub max_most_significant_limb_size: usize,

    pub(super) _max_unreduced_limb: BigUint,
    pub(super) _max_unreduced_value: BigUint,

    _marker: PhantomData<W>,
}

impl<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>
    Rns<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>
{
    pub fn construct() -> Self {
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

        let max_limb = (one << LIMB_SIZE) - 1usize;

        // assert that number of limbs is set correctly
        assert_eq!(
            NUMBER_OF_LIMBS,
            div_ceil(wrong_modulus.bits() as usize, LIMB_SIZE)
        );

        // Max remainder is next power of two of wrong modulus.
        // Witness remainder might overflow the wrong modulus but it is limited
        // to the next power of two of the wrong modulus.
        let max_remainder = (one << wrong_modulus.bits()) - 1usize;

        // with a conservative margin we start with max operand is equal to max remainder approximation
        let pre_binary_modulus = max_remainder.pow(2) / native_modulus;
        let pre_binary_modulus_size = pre_binary_modulus.bits() as usize;
        let mut number_of_carries = div_ceil(pre_binary_modulus_size, LIMB_SIZE);

        // rounding down max quotient and max operand to `2^k - 1` for cheaper range checks
        // may result in a smaller binary modulus so we need to refine number of carries and
        // binary modulus size
        let n_try = 2;

        // TODO: also try to maximize max operand and max quotient under the same binary modulus?

        let (number_of_carries, binary_modulus, crt_modulus, max_quotient, max_operand) = (0
            ..n_try)
            .find_map(|i| {
                println!(
                    "RNS construction, limb_size: {}, try: {}, number_of_carries {}",
                    LIMB_SIZE, i, number_of_carries
                );
                let binary_modulus_size = number_of_carries * LIMB_SIZE;
                let binary_modulus = one << binary_modulus_size;
                let crt_modulus = &binary_modulus * native_modulus;

                // find max quotient
                // first value is not power of two minus one
                let pre_max_quotient = (&crt_modulus - &max_remainder) / wrong_modulus;
                // so lets floor it to there
                let max_quotient = (one << (pre_max_quotient.bits() - 1)) - 1usize;

                // `op * op < q * w + r`
                let tt = &max_quotient * wrong_modulus + &max_remainder;
                let pre_max_operand = tt.sqrt();
                let max_operand = log_floor!(pre_max_operand) - 1usize;

                if &max_quotient < wrong_modulus {
                    println!("q < w");
                    number_of_carries += 1; // TODO consider increasing number of carries
                    return None;
                }
                if &max_operand < wrong_modulus {
                    println!("op < w");
                    number_of_carries += 1; // TODO consider increasing number of carries
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

        let max_most_significant_limb = &max_remainder >> ((NUMBER_OF_LIMBS - 1) * LIMB_SIZE);
        let max_most_significant_limb_size = max_most_significant_limb.bits() as usize;
        let max_remainder_limbs = std::iter::repeat_with(|| max_limb.clone())
            .take(NUMBER_OF_LIMBS - 1)
            .chain(std::iter::once(max_most_significant_limb))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let max_most_significant_limb = &max_quotient >> ((NUMBER_OF_LIMBS - 1) * LIMB_SIZE);
        let max_quotient_limbs = std::iter::repeat_with(|| max_limb.clone())
            .take(NUMBER_OF_LIMBS - 1)
            .chain(std::iter::once(max_most_significant_limb))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let max_most_significant_limb = &max_operand >> ((NUMBER_OF_LIMBS - 1) * LIMB_SIZE);
        let max_operand_limbs = std::iter::repeat_with(|| max_limb.clone())
            .take(NUMBER_OF_LIMBS - 1)
            .chain(std::iter::once(max_most_significant_limb))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let max_reduction_quotient = (one << LIMB_SIZE) - one;
        let max_unreduced_value = wrong_modulus * max_reduction_quotient.clone();
        // 1.5x of the max reduced limb
        let max_unreduced_limb = &(one << (LIMB_SIZE + LIMB_SIZE / 2)) - one;

        // negative wrong field modulus moduli binary modulus `w'`
        // `w' = (T - w)`
        // `w' = [w'_0, w'_1, ... ]`
        let big_neg_wrong_in_binary = binary_modulus - wrong_modulus;
        let big_neg_wrong_limbs_in_binary =
            decompose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&big_neg_wrong_in_binary);

        let neg_wrong_limbs_in_binary: [N; NUMBER_OF_LIMBS] = big_neg_wrong_limbs_in_binary
            .iter()
            .map(big_to_fe_unsafe)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let big_wrong_limbs = decompose::<NUMBER_OF_LIMBS, LIMB_SIZE>(wrong_modulus);
        let wrong_limbs: [N; NUMBER_OF_LIMBS] = big_wrong_limbs
            .iter()
            .map(big_to_fe)
            .collect::<Vec<N>>()
            .try_into()
            .unwrap();
        // `w-1 = [w_0-1 , w_1, ... ] `

        let wrong_in_native: N = big_to_fe(&(wrong_modulus % native_modulus));

        // Calculate shifter elements
        let two = N::from(2);
        // Left shifts field element by `u * LIMB_SIZE` bits
        let left_shifters: [N; NUMBER_OF_LIMBS] = (0..NUMBER_OF_LIMBS)
            .map(|i| two.pow([(i * LIMB_SIZE) as u64, 0, 0, 0]))
            .collect::<Vec<N>>()
            .try_into()
            .unwrap();
        let right_shifters: [N; NUMBER_OF_LIMBS] = left_shifters
            .iter()
            .map(|e| e.invert().unwrap())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        Self {
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

    pub fn max_values(&self, range: Range) -> [BigUint; NUMBER_OF_LIMBS] {
        match range {
            Range::Remainder => self.max_remainder_limbs.clone(),
            Range::Operand => self.max_operand_limbs.clone(),
            Range::Unreduced => std::iter::repeat_with(|| self._max_unreduced_limb.clone())
                .take(NUMBER_OF_LIMBS)
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
            Range::MulQuotient => self.max_quotient_limbs.clone(),
        }
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
                .map(|quotient| assert!(quotient < &self.max_reduction_quotient));
        }
        let quotient = quotient.map(|quotient| big_to_fe_unsafe(&quotient));
        let result = UnassignedInteger::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>::from_big(result);

        (result, quotient)
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn mul_witness(
        &self,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        to_add: &[&Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>],
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

        let quotient = UnassignedInteger::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>::from_big(quotient);
        let result = UnassignedInteger::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>::from_big(result);

        (result, quotient)
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn neg_mul_add_div_witness(
        &self,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        denom: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        to_add: &[&Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>],
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

        let quotient = UnassignedInteger::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>::from_big(quotient);
        let result = UnassignedInteger::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>::from_big(result);

        (result, quotient)
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

        let quotient = UnassignedInteger::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>::from_big(quotient);
        let result = UnassignedInteger::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>::from_big(result);
        let shifter = ConstantInteger::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>::from_big(shifter);

        (result, quotient, shifter)
    }

    pub(crate) fn mul_max_carries(
        &self,
        w0: &[BigUint; NUMBER_OF_LIMBS],
        w1: &[BigUint; NUMBER_OF_LIMBS],
        to_add: &[&[BigUint; NUMBER_OF_LIMBS]],
    ) -> Vec<usize> {
        let mut carry_max = BigUint::zero();
        let ww = schoolbook::<BigUint, BigUint, BigUint>(w0, w1);
        let pq = schoolbook::<BigUint, BigUint, BigUint>(
            &self.max_quotient_limbs,
            &self.big_neg_wrong_limbs_in_binary,
        ); // TODO: precompute

        // transpose
        let to_add = (0..self.number_of_carries)
            .map(|i| to_add.iter().map(|e| e[i].clone()).collect::<Vec<_>>());

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
                carry_max = t >> LIMB_SIZE;
                carry_max.bits() as usize
            })
            .collect()
    }

    pub(crate) fn neg_mul_div_max_carries(
        &self,
        w0: &[BigUint; NUMBER_OF_LIMBS],
        w1: &[BigUint; NUMBER_OF_LIMBS],
        divisor: &[BigUint; NUMBER_OF_LIMBS],
        to_add: &[&[BigUint; NUMBER_OF_LIMBS]],
    ) -> Vec<usize> {
        let mut carry_max = BigUint::zero();
        let ww = schoolbook::<BigUint, BigUint, BigUint>(w0, w1);
        let pq = schoolbook::<BigUint, BigUint, BigUint>(
            &self.max_quotient_limbs,
            &self.big_neg_wrong_limbs_in_binary,
        ); // TODO: precompute
        let rd = schoolbook::<BigUint, BigUint, BigUint>(&self.max_remainder_limbs, divisor);

        // transpose
        let to_add = (0..self.number_of_carries)
            .map(|i| to_add.iter().map(|e| e[i].clone()).collect::<Vec<_>>());

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
                carry_max = t >> LIMB_SIZE;
                carry_max.bits() as usize
            })
            .collect()
    }
}
