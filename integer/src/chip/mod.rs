use crate::integer::Integer;
use ark_std::iterable::Iterable;
use ff::PrimeField;
use halo2::circuit::Value;
use num_bigint::BigUint;
use num_traits::{One, Zero};

use crate::{
    integer::{Range, UnassignedInteger},
    rns::Rns,
};

mod add;
mod assign;
mod mul;
mod reduce;

use std::collections::BTreeMap;

use circuitry::{
    chip::{
        first_degree::FirstDegreeChip, second_degree::SecondDegreeChip, select::SelectChip, Core,
        ROMChip,
    },
    stack::Stack,
    utils::{big_to_fe, big_to_fe_unsafe, compose, compose_into, decompose, fe_to_big, modulus},
    witness::{Composable, Scaled, Witness},
};

impl<
        W: PrimeField,
        N: PrimeField + Ord,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    > IntegerChip<W, N, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>
{
    pub(crate) fn is_gt_max_operand(&self, a: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>) -> bool {
        a.max() > self.rns.max_operand
    }

    pub(crate) fn is_gt_max_remainder(
        &self,
        a: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> bool {
        a.max() > self.rns.max_remainder
    }
}

#[derive(Debug, Clone)]
pub struct IntegerChip<
    W: PrimeField,
    N: PrimeField + Ord,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const SUBLIMB_SIZE: usize,
> {
    pub(crate) rns: Rns<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    pub(super) base_sub_aux: [BigUint; NUMBER_OF_LIMBS],
    pub(super) subtraction_aux:
        BTreeMap<usize, ([N; NUMBER_OF_LIMBS], [BigUint; NUMBER_OF_LIMBS], N)>,
}

fn calculate_base_sub_aux<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
>(
    rns: &Rns<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
) -> [BigUint; NUMBER_OF_LIMBS] {
    let two = N::from(2);
    let r = &fe_to_big(&two.pow([LIMB_SIZE as u64, 0, 0, 0]));
    let wrong_modulus = modulus::<W>();
    let wrong_limbs_big = decompose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&wrong_modulus);
    let wrong_limbs: [N; NUMBER_OF_LIMBS] = wrong_limbs_big
        .iter()
        .map(|limb| big_to_fe_unsafe(limb))
        .collect::<Vec<N>>()
        .try_into()
        .unwrap();

    // `base_aux = 2 * wrong_modulus`
    let mut aux: Vec<BigUint> = wrong_limbs
        .iter()
        .map(|limb| fe_to_big(&limb) << 1usize)
        .collect();

    // If value of a limb is not above dense limb borrow from the next one
    for i in 0..NUMBER_OF_LIMBS - 1 {
        let hidx = NUMBER_OF_LIMBS - i - 1;
        let lidx = hidx - 1;

        if (aux[lidx].bits() as usize) < (LIMB_SIZE + 1) {
            aux[hidx] = aux[hidx].clone() - 1usize;
            aux[lidx] = aux[lidx].clone() + r;
        }
    }

    let aux: [BigUint; NUMBER_OF_LIMBS] = aux.try_into().unwrap();

    {
        let base_aux_value = compose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&aux);
        // Must be equal to wrong modulus
        assert!(base_aux_value.clone() % &rns.wrong_modulus == BigUint::zero());
        // Expected to be above next power of two
        assert!(base_aux_value > rns.max_remainder);
        // Assert limbs are above max values
        for (aux_limb, rem_limb) in aux.iter().zip(rns.max_remainder_limbs.iter()) {
            assert!(aux_limb >= rem_limb);
        }
    }

    aux
}

fn shift_sub_aux<N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>(
    base_sub_aux: &[BigUint; NUMBER_OF_LIMBS],
    shift: usize,
) -> ([N; NUMBER_OF_LIMBS], [BigUint; NUMBER_OF_LIMBS], N) {
    let aux_big: [BigUint; NUMBER_OF_LIMBS] = base_sub_aux
        .iter()
        .map(|aux_limb| aux_limb << shift)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let aux = aux_big
        .iter()
        .map(|e| big_to_fe(e))
        .collect::<Vec<N>>()
        .try_into()
        .unwrap();
    let native = compose_into::<N, N, NUMBER_OF_LIMBS, LIMB_SIZE>(&aux);
    (aux, aux_big, native)
}

impl<
        W: PrimeField,
        N: PrimeField + Ord,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    > IntegerChip<W, N, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>
{
    pub fn rns(&self) -> &Rns<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        &self.rns
    }

    pub(crate) fn get_sub_aux(
        &self,
        max_vals: &[BigUint; NUMBER_OF_LIMBS],
    ) -> ([N; NUMBER_OF_LIMBS], [BigUint; NUMBER_OF_LIMBS], N) {
        let mut max_shift = 0usize;

        for (max_val, aux) in max_vals.iter().zip(self.base_sub_aux.iter()) {
            let mut shift = 1;
            let mut aux = aux.clone();
            while *max_val > aux {
                aux <<= 1usize;
                max_shift = std::cmp::max(shift, max_shift);
                shift += 1;
            }
        }

        match self.subtraction_aux.get(&max_shift) {
            Some(aux) => aux.clone(),
            None => {
                println!("requied to calculate new sub aux at {max_shift}");
                shift_sub_aux::<N, NUMBER_OF_LIMBS, LIMB_SIZE>(&self.base_sub_aux, max_shift)
            }
        }
    }

    pub fn new(rns: &Rns<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>) -> Self {
        let base_sub_aux = calculate_base_sub_aux::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>(rns);
        let subtraction_aux = (0..50)
            .map(|shift| {
                (
                    shift,
                    shift_sub_aux::<N, NUMBER_OF_LIMBS, LIMB_SIZE>(&base_sub_aux, shift),
                )
            })
            .collect::<BTreeMap<_, _>>();

        Self {
            rns: rns.clone(),
            base_sub_aux,
            subtraction_aux,
        }
    }
}

impl<
        W: PrimeField,
        N: PrimeField + Ord,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    > IntegerChip<W, N, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>
{
    pub fn sign(
        &self,
        stack: &mut Stack<N>,
        w: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Witness<N> {
        self.assert_in_field(stack, w);
        let limb0 = w.limb_at(0);
        let (sign, half) = limb0
            .value()
            .map(|value| {
                let value = &fe_to_big(&value);
                let half = big_to_fe::<N>(&(value >> 1usize));
                let sign: N = ((value & BigUint::one() != BigUint::zero()) as u64).into();
                (sign, half)
            })
            .unzip();
        let sign = stack.assign_bit(sign);
        let half = stack.new_witness(half);
        let terms = [half * N::from(2), sign.add(), limb0.sub()];
        stack.zero_sum(&terms[..], N::ZERO);
        sign
    }

    pub fn assert_not_zero(
        &self,
        stack: &mut Stack<N>,
        w: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        let is_zero = self.is_zero(stack, w);
        stack.assert_zero(&is_zero);
    }

    pub fn is_zero(
        &self,
        stack: &mut Stack<N>,
        w: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Witness<N> {
        let w = self.reduce(stack, w);
        self.assert_in_field(stack, &w);
        let mut acc: Option<Witness<N>> = None;
        w.limbs().iter().for_each(|limb| {
            let is_zero = stack.is_zero(&limb);
            let _acc = acc.map_or(is_zero, |acc| stack.mul(&is_zero, &acc));
            acc = Some(_acc);
        });
        acc.unwrap()
    }

    pub fn is_one(
        &self,
        stack: &mut Stack<N>,
        w: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Witness<N> {
        let w = self.reduce(stack, w);
        self.assert_in_field(stack, &w);
        let mut acc = stack.is_one(w.limb_at(0));
        w.limbs().iter().skip(1).for_each(|limb| {
            let is_zero = stack.is_zero(&limb);
            acc = stack.mul(&is_zero, &acc);
        });
        acc
    }

    pub fn assert_in_field(
        &self,
        stack: &mut Stack<N>,
        w: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        let mut borrows = vec![];
        let mut prev_borrow = BigUint::zero();
        let result: Vec<_> = w
            .limbs()
            .iter()
            .zip(self.rns.big_wrong_limbs.iter())
            .enumerate()
            .map(|(i, (w, modulus_limb))| {
                let is_last = i == (NUMBER_OF_LIMBS - 1);
                let modulus_limb = if is_last {
                    modulus_limb - 1usize
                } else {
                    modulus_limb.clone()
                };
                let w = w.big();
                let (limb, borrow) = w
                    .map(|w| {
                        //
                        let cur_borrow = if modulus_limb < &w + &prev_borrow {
                            BigUint::one()
                        } else {
                            BigUint::zero()
                        };
                        let limb =
                            ((modulus_limb + (&cur_borrow << LIMB_SIZE)) - &prev_borrow) - &w;
                        prev_borrow = cur_borrow;

                        (big_to_fe::<N>(&limb), big_to_fe::<N>(&prev_borrow))
                    })
                    .unzip();

                if !is_last {
                    borrows.push(stack.assign_bit(borrow));
                }

                limb
            })
            .collect();

        let lsh = self.rns.left_shifters[1];
        let result: Value<Vec<N>> = Value::from_iter(result);
        let result = result.map(|limbs| limbs.try_into().unwrap());
        let result = UnassignedInteger::from_limbs(result);
        let result = self.range(stack, &result, Range::Remainder);

        // first
        let terms = [
            w.limb_at(0).sub(),
            result.limb_at(0).sub(),
            borrows[0] * lsh,
        ];
        stack.zero_sum(&terms[..], self.rns.wrong_limbs[0]);
        // intermediate
        for i in 1..NUMBER_OF_LIMBS - 1 {
            let terms = [
                w.limb_at(i).sub(),
                result.limb_at(i).sub(),
                borrows[i] * lsh,
                borrows[i - 1].sub(),
            ];
            stack.zero_sum(&terms[..], self.rns.wrong_limbs[i]);
        }
        // last
        let terms = [
            w.limb_at(NUMBER_OF_LIMBS - 1).sub(),
            result.limb_at(NUMBER_OF_LIMBS - 1).sub(),
            borrows[NUMBER_OF_LIMBS - 2].sub(),
        ];
        stack.zero_sum(
            &terms[..],
            self.rns.wrong_limbs[NUMBER_OF_LIMBS - 1] - N::ONE,
        );
    }

    pub fn reduce_external<T: PrimeField>(
        &self,
        stack: &mut Stack<N>,
        a: &Integer<T, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let max_values = self.rns.max_values(Range::Remainder);
        let a = Integer::new(a.limbs(), &max_values, a.big(), *a.native());
        self.reduce(stack, &a);
        a
    }

    // TODO: this is not sound. use only in tests
    pub fn assign(
        &self,
        stack: &mut Stack<N>,
        integer: UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        range: Range,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let limbs: Vec<Witness<N>> = integer
            .limbs()
            .iter()
            .map(|limb| stack.new_witness(limb))
            .collect();

        let max_values = self.rns.max_values(range);

        let terms: Vec<Scaled<N>> = limbs
            .iter()
            .zip(self.rns.left_shifters.iter())
            .map(|(limb, base)| Scaled::new(limb, base))
            .collect();
        let native = stack.compose(&terms[..], N::ZERO);

        Integer::new(
            &limbs.try_into().unwrap(),
            &max_values,
            integer.big(),
            native,
        )
    }

    pub fn copy_equal(
        &self,
        stack: &mut Stack<N>,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        w0.limbs().iter().zip(w1.limbs()).for_each(|(w0, w1)| {
            stack.equal(&w0, w1);
        });
    }

    pub fn normal_equal(
        &self,
        stack: &mut Stack<N>,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        let dif = &self.sub(stack, w0, w1);
        self.assert_zero(stack, dif)
    }

    pub fn assert_not_equal(
        &self,
        stack: &mut Stack<N>,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        let dif = &self.sub(stack, w0, w1);
        self.assert_not_zero(stack, dif)
    }

    pub fn select(
        &self,
        stack: &mut Stack<N>,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        cond: &Witness<N>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let limbs = w0
            .limbs()
            .iter()
            .zip(w1.limbs().iter())
            .map(|(w0, w1)| stack.select(cond, &w0, &w1))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let native = stack.select(cond, w0.native(), w1.native());

        let max_vals = w0
            .max_vals()
            .iter()
            .zip(w1.max_vals().iter())
            .map(|(w0, w1)| std::cmp::max(w0, w1).clone())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let big = w0
            .big()
            .zip(w1.big())
            .zip(cond.value())
            .map(|((w0, w1), cond)| {
                if cond == N::ONE {
                    w0
                } else {
                    #[cfg(feature = "prover-sanity")]
                    {
                        assert_eq!(cond, N::ZERO);
                    }
                    w1
                }
            });

        Integer::new(&limbs, &max_vals, big, native)
    }

    pub fn write(
        &self,
        stack: &mut Stack<N>,
        tag: N,
        address: N,
        integer: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        assert!(!self.is_gt_max_remainder(integer));
        stack.write(tag, address, integer.limbs());
    }

    pub fn read_recover(
        &self,
        stack: &mut Stack<N>,
        tag: N,
        address_base: N,
        address_fraction: &Witness<N>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let limbs = stack.read(tag, address_base, address_fraction);

        // recover native value
        let terms: Vec<Scaled<N>> = limbs
            .iter()
            .zip(self.rns.left_shifters.iter())
            .map(|(limb, base)| Scaled::new(limb, base))
            .collect();
        let native = stack.compose(&terms[..], N::ZERO);

        // find the big
        let values = limbs.iter().map(|limb| limb.value()).collect::<Vec<_>>();
        let values: Value<Vec<N>> = Value::from_iter(values);
        let big = values.map(|values| {
            let limbs = values.iter().map(fe_to_big).collect::<Vec<_>>();
            compose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&limbs.try_into().unwrap())
        });

        // written value is asumed to be in remeinder range
        let max_values = self.rns.max_values(Range::Remainder);

        Integer::new(&limbs.try_into().unwrap(), &max_values, big, native)
    }
}
