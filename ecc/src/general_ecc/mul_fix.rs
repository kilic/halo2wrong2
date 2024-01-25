use super::GeneralEccChip;
use crate::Point;
use circuitry::{
    chip::{range::RangeChip, Core},
    stack::Stack,
    witness::{Composable, Witness},
};
use ff::PrimeField;
use group::{Curve, Group};
use halo2::halo2curves::CurveAffine;
use integer::integer::Integer;

pub struct FixMul<
    Emulated: CurveAffine,
    N: PrimeField + Ord,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
> {
    pub table: Vec<Vec<Point<Emulated::Base, N, NUMBER_OF_LIMBS, LIMB_SIZE>>>,
    pub correction: Point<Emulated::Base, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
}

macro_rules! div_ceil {
    ($a:expr, $b:expr) => {
        (($a - 1) / $b) + 1
    };
}

impl<
        Emulated: CurveAffine,
        N: PrimeField + Ord,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    > GeneralEccChip<Emulated, N, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>
{
    pub fn prepare_mul_fix(
        &self,
        stack: &mut Stack<N>,
        point: Emulated,
    ) -> FixMul<Emulated, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let window_size = 4usize;

        pub(crate) fn binary_table<C: CurveAffine>(
            point: C,
            aux: C::CurveExt,
            window_size: usize,
        ) -> Vec<Vec<C::CurveExt>> {
            pub(crate) fn incremental_table<C: CurveAffine>(
                point: C::CurveExt,
                size: usize,
                aux: C::CurveExt,
            ) -> Vec<C::CurveExt> {
                assert!(size > 0);
                let mut acc = aux.clone();
                (0..size)
                    .map(|i| {
                        let ret = acc;
                        if i != size - 1 {
                            acc += point;
                        }
                        ret
                    })
                    .collect()
            }

            let table = incremental_table::<C>(point.to_curve(), 1 << window_size, aux);
            let number_of_rounds = div_ceil!(C::ScalarExt::NUM_BITS as usize, window_size);
            let mut tables: Vec<Vec<C::CurveExt>> = vec![table.clone()];
            for i in 0..number_of_rounds - 1 {
                let table: Vec<C::CurveExt> = tables[i]
                    .iter()
                    .map(|p| (0..window_size).fold(*p, |acc, _| acc.double()))
                    .collect::<Vec<_>>();
                tables.push(table);
            }
            tables
        }

        let mut aux = self.constant_aux.to_curve();
        let table = binary_table(point, aux, window_size);

        let mut correction = Emulated::CurveExt::identity();
        (0..table.len()).for_each(|_| {
            correction += aux;
            aux = (0..window_size).fold(aux.clone(), |e, _| e.double());
        });

        let correction = self.register_constant(stack, correction.to_affine().neg());

        let table = table
            .iter()
            .map(|table| {
                table
                    .iter()
                    // TODO: batch affine
                    .map(|e| self.register_constant(stack, e.to_affine()))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        FixMul { table, correction }
    }

    pub fn mul_fix(
        &self,
        stack: &mut Stack<N>,
        prepared: &FixMul<Emulated, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        scalar: &Integer<Emulated::Scalar, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Point<Emulated::Base, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let window_size = 4;

        let scalar = scalar
            .limbs()
            .iter()
            .enumerate()
            .flat_map(|(i, limb)| {
                let word_size = if i == NUMBER_OF_LIMBS - 1 {
                    self.ch_base.rns().max_most_significant_limb_size
                } else {
                    LIMB_SIZE
                };

                let (_scalar, bits) = stack.decompose(limb.value(), word_size, 1);
                stack.equal(&_scalar, limb);
                bits
            })
            .collect::<Vec<_>>();

        let scalar = scalar
            .chunks(window_size)
            .map(|chunk| chunk.to_vec())
            .collect::<Vec<_>>();

        let mut add_chain = Vec::with_capacity(prepared.table.len());
        add_chain.push(prepared.correction.clone());

        scalar
            .iter()
            .zip(prepared.table.iter())
            .for_each(|(selector, table)| {
                add_chain.push(self.select_multi(stack, selector, table));
            });

        self.add_multi(stack, &add_chain[..])
    }
}
