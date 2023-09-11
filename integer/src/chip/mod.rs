use crate::integer::Integer;
use ff::PrimeField;
use num_bigint::BigUint;

use crate::{
    integer::{Range, UnassignedInteger},
    rns::Rns,
};

mod add;
mod assert_not_zero;
mod assign;
mod mul;
mod reduce;

impl<
        W: PrimeField,
        N: PrimeField + Ord,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const NUMBER_OF_SUBLIMBS: usize,
        const SUBLIMB_SIZE: usize,
    > IntegerChip<W, N, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>
{
    pub(crate) fn is_gt_max_operand(&self, a: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>) -> bool {
        a.max() > self.rns.max_operand
    }

    pub(crate) fn reduce_if_gt_max_operand<Stack: SecondDegreeChip<N> + FirstDegreeChip<N>>(
        &self,
        stack: &mut Stack,

        a: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        if self.is_gt_max_operand(a) {
            // here to signal mostly unexpected behavior
            println!("GT MAX OPERAND!");
            self.reduce(stack, a)
        } else {
            a.clone()
        }
    }
}

use std::collections::BTreeMap;

use circuitry::{
    chip::{
        first_degree::FirstDegreeChip, second_degree::SecondDegreeChip, select::SelectChip, Chip,
        Core,
    },
    utils::{big_to_fe_unsafe, compose_into},
    witness::{Composable, Scaled, Witness},
};

// pub trait CRT256Chip<F: PrimeField + Ord, const NUMBER_OF_LIMBS: usize>:
//     Chip<CRT256Enforcement<F, NUMBER_OF_LIMBS>, F>
// {
//     fn big_mul(
//         &mut self,
//         w0: &[Witness<F>; NUMBER_OF_LIMBS],
//         w1: &[Witness<F>; NUMBER_OF_LIMBS],
//         result: &[Witness<F>; NUMBER_OF_LIMBS],
//         quotient: &[Witness<F>; NUMBER_OF_LIMBS],
//         carries: &[Witness<F>; NUMBER_OF_LIMBS],
//         to_sub: &[Witness<F>; NUMBER_OF_LIMBS],
//     ) {
//         self.new_op(CRT256Enforcement::Mul {
//             w0: w0.clone(),
//             w1: w1.clone(),
//             result: result.clone(),
//             quotient: quotient.clone(),
//             carries: carries.clone(),
//             to_sub: to_sub.clone(),
//         })
//     }

//     fn big_red(
//         &mut self,
//         w0: &[Witness<F>; NUMBER_OF_LIMBS],
//         result: &[Witness<F>; NUMBER_OF_LIMBS],
//         carries: &[Witness<F>; NUMBER_OF_LIMBS],
//         quotient: &Witness<F>,
//     ) {
//         self.new_op(CRT256Enforcement::Reduce {
//             w0: w0.clone(),
//             result: result.clone(),
//             carries: carries.clone(),
//             quotient: *quotient,
//         })
//     }
// }

#[derive(Debug)]
pub struct IntegerChip<
    W: PrimeField,
    N: PrimeField + Ord,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const NUMBER_OF_SUBLIMBS: usize,
    const SUBLIMB_SIZE: usize,
> {
    pub(crate) rns: Rns<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    pub(super) subtraction_aux:
        BTreeMap<usize, ([N; NUMBER_OF_LIMBS], [BigUint; NUMBER_OF_LIMBS], N)>,
}

impl<
        W: PrimeField,
        N: PrimeField + Ord,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const NUMBER_OF_SUBLIMBS: usize,
        const SUBLIMB_SIZE: usize,
    > IntegerChip<W, N, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>
{
    pub fn rns(&self) -> &Rns<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        &self.rns
    }

    pub fn new(rns: &Rns<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>) -> Self {
        let subtraction_aux = (0..50)
            .map(|shift| (shift, Self::calculate_sub_aux(rns, shift)))
            .collect::<BTreeMap<_, _>>();
        Self {
            rns: rns.clone(),

            subtraction_aux,
        }
    }

    fn calculate_sub_aux(
        rns: &Rns<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        shift: usize,
    ) -> ([N; NUMBER_OF_LIMBS], [BigUint; NUMBER_OF_LIMBS], N) {
        let aux_big: [BigUint; NUMBER_OF_LIMBS] = rns
            .base_aux
            .iter()
            .map(|aux_limb| aux_limb << shift)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let aux = aux_big
            .iter()
            .map(|e| big_to_fe_unsafe(e))
            .collect::<Vec<N>>()
            .try_into()
            .unwrap();
        let native = compose_into::<N, N, NUMBER_OF_LIMBS, LIMB_SIZE>(&aux);
        (aux, aux_big, native)
    }
}

impl<
        W: PrimeField,
        N: PrimeField + Ord,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const NUMBER_OF_SUBLIMBS: usize,
        const SUBLIMB_SIZE: usize,
    > IntegerChip<W, N, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>
{
    pub(crate) fn subtracion_aux(
        &self,
        max_vals: &[BigUint; NUMBER_OF_LIMBS],
    ) -> ([N; NUMBER_OF_LIMBS], [BigUint; NUMBER_OF_LIMBS], N) {
        let mut max_shift = 0usize;

        for (max_val, aux) in max_vals.iter().zip(self.rns.base_aux.iter()) {
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
                Self::calculate_sub_aux(&self.rns, max_shift)
            }
        }
    }

    pub fn assign(
        &self,
        stack: &mut impl FirstDegreeChip<N>,
        integer: UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        range: Range,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let limbs: Vec<Witness<N>> = integer
            .limbs()
            .transpose_vec(NUMBER_OF_LIMBS)
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
            &limbs.try_into().unwrap(),
            &max_values,
            integer.big(),
            native,
        )
    }

    pub fn copy_equal(
        &self,
        stack: &mut impl Core<N>,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        w0.limbs().iter().zip(w1.limbs()).for_each(|(w0, w1)| {
            stack.equal(w0, w1);
        });
    }

    // pub fn to_bits(
    //     &self,
    //     stack: CRTChip<N,NUMBER_OF_LIMBS>,
    //     integer: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    // ) -> Vec<Witness<N>> {
    //     let decomposed: Vec<Witness<N>> = (0..NUMBER_OF_LIMBS)
    //         .flat_map(|idx| stack.decompose::<LIMB_SIZE, 1>(&integer.limbs[idx]))
    //         .collect();
    //     assert_eq!(decomposed.len(), self.rns.wrong_modulus.bits() as usize);
    //     decomposed
    // }

    pub fn normal_equal<Stack: SecondDegreeChip<N> + FirstDegreeChip<N>>(
        &self,
        stack: &mut Stack,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        let must_be_zero = &self.sub(stack, w0, w1);
        self.assert_zero(stack, must_be_zero)
    }

    pub fn assert_not_equal<Stack: SecondDegreeChip<N> + FirstDegreeChip<N>>(
        &self,
        stack: &mut Stack,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        let c = &self.sub(stack, w0, w1);
        self.assert_not_zero(stack, c)
    }

    pub fn select(
        &self,
        stack: &mut impl SelectChip<N>,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        cond: &Witness<N>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let limbs = w0
            .limbs()
            .iter()
            .zip(w1.limbs.iter())
            .map(|(w0, w1)| stack.select(cond, w0, w1))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let native = stack.select(cond, &w0.native, &w1.native);

        let max_vals = w0
            .max_vals
            .iter()
            .zip(w1.max_vals.iter())
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
                    #[cfg(feature = "sanity-check")]
                    {
                        assert_eq!(cond, N::ZERO);
                    }
                    w1
                }
            });

        Integer::new(&limbs, &max_vals, big, native)
    }

    // pub fn assert_bit(
    //     &self,
    //     stack: &mut impl ArithmeticChip<N>,
    //     w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    // ) {
    //     for limb in w0.limbs().iter().skip(1) {
    //         stack.assert_zero(limb);
    //     }
    //     stack.assert_bit(w0.limbs().first().unwrap())
    // }
}
