use crate::integer::Integer;
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
    utils::{big_to_fe, big_to_fe_unsafe, compose, fe_to_big, modulus},
    witness::{Composable, Scaled, Witness},
};

impl<W: PrimeField, N: PrimeField + Ord> IntegerChip<W, N> {
    pub(crate) fn is_gt_max_operand(&self, a: &Integer<W, N>) -> bool {
        a.max() > self.rns.max_operand
    }

    pub(crate) fn is_gt_max_remainder(&self, a: &Integer<W, N>) -> bool {
        a.max() > self.rns.max_remainder
    }
}

#[derive(Debug, Clone)]
pub struct IntegerChip<W: PrimeField, N: PrimeField + Ord> {
    pub(crate) sublimb_size: usize,
    pub(crate) rns: Rns<W, N>,
    pub(super) base_sub_aux: Vec<BigUint>,
    pub(super) subtraction_aux: BTreeMap<usize, (Vec<N>, Vec<BigUint>, N)>,
}

fn calculate_base_sub_aux<W: PrimeField, N: PrimeField>(rns: &Rns<W, N>) -> Vec<BigUint> {
    let two = N::from(2);
    let r = &fe_to_big(&two.pow([rns.limb_size as u64, 0, 0, 0]));
    let wrong_modulus = modulus::<W>();
    let wrong_limbs_big = rns.decompose(&wrong_modulus);
    let wrong_limbs = wrong_limbs_big
        .iter()
        .map(|limb| big_to_fe_unsafe(limb))
        .collect::<Vec<N>>();

    // `base_aux = 2 * wrong_modulus`
    let mut aux: Vec<BigUint> = wrong_limbs
        .iter()
        .map(|limb| fe_to_big(limb) << 1usize)
        .collect();

    // If value of a limb is not above dense limb borrow from the next one
    for i in 0..rns.number_of_limbs - 1 {
        let hidx = rns.number_of_limbs - i - 1;
        let lidx = hidx - 1;

        if (aux[lidx].bits() as usize) < (rns.limb_size + 1) {
            aux[hidx] = aux[hidx].clone() - 1usize;
            aux[lidx] = aux[lidx].clone() + r;
        }
    }

    {
        let base_aux_value = compose(&aux, rns.limb_size);
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

impl<W: PrimeField, N: PrimeField + Ord> IntegerChip<W, N> {
    pub fn rns(&self) -> &Rns<W, N> {
        &self.rns
    }

    pub(crate) fn get_sub_aux(&self, max_vals: &[BigUint]) -> (Vec<N>, Vec<BigUint>, N) {
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
                self.rns.shift_sub_aux(&self.base_sub_aux, max_shift)
            }
        }
    }

    pub fn new(rns: &Rns<W, N>, sublimb_size: usize) -> Self {
        let base_sub_aux = calculate_base_sub_aux::<W, N>(rns);
        let subtraction_aux = (0..50)
            .map(|shift| (shift, rns.shift_sub_aux(&base_sub_aux, shift)))
            .collect::<BTreeMap<_, _>>();

        Self {
            rns: rns.clone(),
            base_sub_aux,
            subtraction_aux,
            sublimb_size,
        }
    }
}

impl<W: PrimeField, N: PrimeField + Ord> IntegerChip<W, N> {
    pub fn sign(&self, stack: &mut Stack<N>, w: &Integer<W, N>) -> Witness<N> {
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

    pub fn assert_not_zero(&self, stack: &mut Stack<N>, w: &Integer<W, N>) {
        let is_zero = self.is_zero(stack, w);
        stack.assert_zero(&is_zero);
    }

    pub fn is_zero(&self, stack: &mut Stack<N>, w: &Integer<W, N>) -> Witness<N> {
        let w = self.reduce(stack, w);
        self.assert_in_field(stack, &w);
        let mut acc: Option<Witness<N>> = None;
        w.limbs().iter().for_each(|limb| {
            let is_zero = stack.is_zero(limb);
            let _acc = acc.map_or(is_zero, |acc| stack.mul(&is_zero, &acc));
            acc = Some(_acc);
        });
        acc.unwrap()
    }

    pub fn is_one(&self, stack: &mut Stack<N>, w: &Integer<W, N>) -> Witness<N> {
        let w = self.reduce(stack, w);
        self.assert_in_field(stack, &w);
        let mut acc = stack.is_one(w.limb_at(0));
        w.limbs().iter().skip(1).for_each(|limb| {
            let is_zero = stack.is_zero(limb);
            acc = stack.mul(&is_zero, &acc);
        });
        acc
    }

    pub fn assert_in_field(&self, stack: &mut Stack<N>, w: &Integer<W, N>) {
        let mut borrows = vec![];
        let mut prev_borrow = BigUint::zero();
        let result: Vec<_> = w
            .limbs()
            .iter()
            .zip(self.rns.big_wrong_limbs.iter())
            .enumerate()
            .map(|(i, (w, modulus_limb))| {
                let is_last = i == (self.rns.number_of_limbs - 1);
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
                        let limb = ((modulus_limb + (&cur_borrow << self.rns.limb_size))
                            - &prev_borrow)
                            - &w;
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
        let result =
            UnassignedInteger::from_limbs(result, self.rns.number_of_limbs, self.rns.limb_size);
        let result = self.range(stack, &result, Range::Remainder);

        // first
        let terms = [
            w.limb_at(0).sub(),
            result.limb_at(0).sub(),
            borrows[0] * lsh,
        ];
        stack.zero_sum(&terms[..], self.rns.wrong_limbs[0]);
        // intermediate
        for i in 1..self.rns.number_of_limbs - 1 {
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
            w.limb_at(self.rns.number_of_limbs - 1).sub(),
            result.limb_at(self.rns.number_of_limbs - 1).sub(),
            borrows[self.rns.number_of_limbs - 2].sub(),
        ];
        stack.zero_sum(
            &terms[..],
            self.rns.wrong_limbs[self.rns.number_of_limbs - 1] - N::ONE,
        );
    }

    pub fn reduce_external<T: PrimeField>(
        &self,
        stack: &mut Stack<N>,
        a: &Integer<T, N>,
    ) -> Integer<W, N> {
        let max_values = self.rns.max_values(Range::Remainder);
        let a = Integer::new(
            a.limbs(),
            &max_values,
            a.big(),
            *a.native(),
            self.rns.limb_size,
        );
        self.reduce(stack, &a);
        a
    }

    // TODO: this is not sound. use only in tests
    pub fn assign(
        &self,
        stack: &mut Stack<N>,
        integer: UnassignedInteger<W, N>,
        range: Range,
    ) -> Integer<W, N> {
        let limbs: Vec<Witness<N>> = integer
            .limbs()
            .iter()
            .map(|limb| stack.new_witness(*limb))
            .collect();

        let max_values = self.rns.max_values(range);

        let terms: Vec<Scaled<N>> = limbs
            .iter()
            .zip(self.rns.left_shifters.iter())
            .map(|(limb, base)| Scaled::new(limb, *base))
            .collect();
        let native = stack.compose(&terms[..], N::ZERO);

        Integer::new(
            &limbs,
            &max_values,
            integer.big(),
            native,
            self.rns.limb_size,
        )
    }

    pub fn copy_equal(&self, stack: &mut Stack<N>, w0: &Integer<W, N>, w1: &Integer<W, N>) {
        w0.limbs().iter().zip(w1.limbs()).for_each(|(w0, w1)| {
            stack.equal(w0, w1);
        });
    }

    pub fn normal_equal(&self, stack: &mut Stack<N>, w0: &Integer<W, N>, w1: &Integer<W, N>) {
        let dif = &self.sub(stack, w0, w1);
        self.assert_zero(stack, dif)
    }

    pub fn assert_not_equal(&self, stack: &mut Stack<N>, w0: &Integer<W, N>, w1: &Integer<W, N>) {
        let dif = &self.sub(stack, w0, w1);
        self.assert_not_zero(stack, dif)
    }

    pub fn select(
        &self,
        stack: &mut Stack<N>,
        w0: &Integer<W, N>,
        w1: &Integer<W, N>,
        cond: &Witness<N>,
    ) -> Integer<W, N> {
        let limbs = w0
            .limbs()
            .iter()
            .zip(w1.limbs().iter())
            .map(|(w0, w1)| stack.select(cond, w0, w1))
            .collect::<Vec<_>>();

        let native = stack.select(cond, w0.native(), w1.native());

        let max_vals = w0
            .max_vals()
            .iter()
            .zip(w1.max_vals().iter())
            .map(|(w0, w1)| std::cmp::max(w0, w1).clone())
            .collect::<Vec<_>>();

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

        Integer::new(&limbs, &max_vals, big, native, self.rns.limb_size)
    }

    pub fn write(&self, stack: &mut Stack<N>, tag: N, address: N, integer: &Integer<W, N>) {
        assert!(!self.is_gt_max_remainder(integer));
        stack.write(tag, address, integer.limbs());
    }

    pub fn read_recover(
        &self,
        stack: &mut Stack<N>,
        tag: N,
        address_base: N,
        address_fraction: &Witness<N>,
    ) -> Integer<W, N> {
        let limbs = stack.read(tag, address_base, address_fraction);

        // recover native value
        let terms: Vec<Scaled<N>> = limbs
            .iter()
            .zip(self.rns.left_shifters.iter())
            .map(|(limb, base)| Scaled::new(limb, *base))
            .collect();
        let native = stack.compose(&terms[..], N::ZERO);

        // find the big
        let values = limbs.iter().map(|limb| limb.value()).collect::<Vec<_>>();
        let values: Value<Vec<N>> = Value::from_iter(values);
        let big = values.map(|values| {
            let limbs = values.iter().map(fe_to_big).collect::<Vec<_>>();
            compose(&limbs, self.rns.limb_size)
        });

        // written value is asumed to be in remeinder range
        let max_values = self.rns.max_values(Range::Remainder);

        Integer::new(&limbs, &max_values, big, native, self.rns.limb_size)
    }
}
