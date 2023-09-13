use circuitry::{
    chip::{first_degree::FirstDegreeChip, second_degree::SecondDegreeChip, select::SelectChip},
    utils::{compose, fe_to_big},
    witness::{Composable, Scaled, Witness},
};
use ff::{Field, PrimeField};
use group::{Curve, Group};
use halo2::{circuit::Value, halo2curves::CurveAffine};
use integer::integer::{Integer, UnassignedInteger};
use num_bigint::BigUint;

macro_rules! div_ceil {
    ($a:expr, $b:expr) => {
        (($a - 1) / $b) + 1
    };
}

use crate::{
    utils::{binary_table, mul_fix},
    Point,
};

use super::BaseFieldEccChip;

impl<
        C: CurveAffine,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const NUMBER_OF_SUBLIMBS: usize,
        const SUBLIMB_SIZE: usize,
    > BaseFieldEccChip<C, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>
{
    pub fn msm_sliding_vertical<
        Stack: SecondDegreeChip<C::Scalar> + FirstDegreeChip<C::Scalar> + SelectChip<C::Scalar>,
    >(
        &self,
        stack: &mut Stack,

        points: &[Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>],
        scalars: &[Witness<C::Scalar>],
        window_size: usize,
    ) -> Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let number_of_points = points.len();
        assert!(number_of_points > 0);
        assert_eq!(number_of_points, scalars.len());

        let mut acc = self.assign_point(stack, self.aux_generator);
        let mut acc_aux = None;

        let tables = points
            .chunks(window_size)
            .enumerate()
            .map(|(_, chunk)| {
                let mut table = vec![acc.clone()];

                for (i, point) in chunk.iter().enumerate() {
                    for j in 0..(1 << i) {
                        table.push(self.add_incomplete(stack, &table[j], point));
                    }
                }

                acc_aux = if let Some(acc_aux) = &acc_aux {
                    Some(self.add_incomplete(stack, &acc, &acc_aux))
                } else {
                    Some(acc.clone())
                };

                acc = self.double_incomplete(stack, &acc);
                table
            })
            .collect::<Vec<_>>();

        let scalars = scalars
            .iter()
            .map(|scalar| {
                let (_scalar, mut bits) =
                    stack.decompose_generic(scalar.value(), C::Scalar::NUM_BITS as usize, 1);

                stack.equal(&_scalar, scalar);

                bits.reverse();
                bits
            })
            .collect::<Vec<_>>();

        let acc_aux = acc_aux.unwrap();
        let mut acc = None;
        let mut correction = None;
        for round in 0..(C::Scalar::NUM_BITS as usize) {
            if let Some(_acc) = acc {
                acc = Some(self.double_incomplete(stack, &_acc));
            }

            // TODO: use ladder
            if let Some(_correction) = correction {
                correction = Some(self.double_incomplete(stack, &_correction));
            }
            correction = if let Some(correction) = &correction {
                Some(self.add_incomplete(stack, &correction, &acc_aux))
            } else {
                Some(acc_aux.clone())
            };

            let mut chain = Vec::with_capacity(tables.len() + 1);
            if let Some(acc) = acc {
                chain.push(acc)
            }

            for (_, (table, scalars)) in tables.iter().zip(scalars.chunks(window_size)).enumerate()
            {
                assert_eq!(table.len(), 1 << scalars.len());

                let selector = scalars
                    .iter()
                    .map(|scalar| scalar[round])
                    .collect::<Vec<_>>();

                let to_add = self.select_multi(stack, &selector, table);

                chain.push(to_add);
            }
            acc = Some(self.add_multi(stack, &chain[..]));
        }

        self.sub_incomplete(stack, &acc.unwrap(), &correction.unwrap())
    }

    // fn assign_incremental_table<Stack: SecondDegreeChip<C::Scalar> + FirstDegreeChip<C::Scalar>>(
    //     &self,
    //     stack: &mut Stack,

    //     aux: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
    //     point: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
    //     window_size: usize,
    // ) -> Vec<Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>> {
    //     let table_size = 1 << window_size;
    //     let mut table = vec![aux.clone()];
    //     for i in 0..(table_size - 1) {
    //         table.push(self.add_incomplete(stack, &table[i], point));
    //     }
    //     table
    // }

    // pub fn msm_sliding_horizontal<
    //     Stack: SecondDegreeChip<C::Scalar> + FirstDegreeChip<C::Scalar> + SelectChip<C::Scalar>,
    // >(
    //     &self,
    //     stack: &mut Stack,

    //     points: &[Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>],
    //     scalars: &[Witness<C::Scalar>],
    //     window_size: usize,
    // ) -> Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
    //     let number_of_points = points.len();
    //     assert!(number_of_points > 0);
    //     assert_eq!(number_of_points, scalars.len());

    //     // TODO: correction calculation must be enforced
    //     let correction = self.aux_generator.map(|aux_generator| {
    //         let mut aux = aux_generator.to_curve();
    //         (0..number_of_points)
    //             .fold(C::CurveExt::identity(), |acc, _| {
    //                 let aux_table = binary_table::<C>(&C::identity(), &aux, window_size);
    //                 aux = aux.double();
    //                 acc + mul_fix::<C>(&aux_table[..], &C::ScalarExt::ZERO, window_size)
    //             })
    //             .to_affine()
    //             .neg()
    //     });

    //     let mut aux = self.assign_point(stack, self.aux_generator);
    //     let correction = self.assign_point(stack, correction);

    //     let scalars = scalars
    //         .iter()
    //         .map(|scalar| {
    //             let (_scalar, bits) =
    //                 stack.decompose_generic(scalar.value(), C::Scalar::NUM_BITS as usize, 1);

    //             stack.equal(&_scalar, scalar);

    //             bits.chunks(window_size)
    //                 .rev()
    //                 .map(|chunk| chunk.to_vec())
    //                 .collect::<Vec<_>>()
    //         })
    //         .collect::<Vec<_>>();

    //     let tables: Vec<Vec<Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>>> = points
    //         .iter()
    //         .enumerate()
    //         .map(|(i, point)| {
    //             let table = self.assign_incremental_table(stack, &aux, point, window_size);
    //             if i != number_of_points - 1 {
    //                 aux = self.double_incomplete(stack, &aux);
    //             }
    //             table
    //         })
    //         .collect();

    //     // let mut acc = self.select_multi(stack, &scalars[0][0], &tables[0]);

    //     // for (table, windowed) in tables.iter().skip(1).zip(scalars.iter().skip(1)) {
    //     //     let selector = &windowed[0];
    //     //     let to_add = self.select_multi(stack, selector, table);

    //     //     acc = self.add_incomplete(stack, &acc, &to_add);
    //     // }

    //     // let number_of_windows = div_ceil!(C::Scalar::NUM_BITS as usize, window_size);
    //     // for i in 1..number_of_windows {
    //     //     for _ in 0..window_size {
    //     //         acc = self.double_incomplete(stack, &acc);
    //     //     }

    //     //     for (table, windowed) in tables.iter().zip(scalars.iter()) {
    //     //         let selector = &windowed[i];
    //     //         let to_add = self.select_multi(stack, selector, table);
    //     //         acc = self.add_incomplete(stack, &acc, &to_add);
    //     //     }
    //     // }

    //     // let mut acc = self.select_multi(stack, &scalars[0][0], &tables[0]);

    //     // for (table, windowed) in tables.iter().skip(1).zip(scalars.iter().skip(1)) {
    //     //     let selector = &windowed[0];
    //     //     let to_add = self.select_multi(stack, selector, table);

    //     //     acc = self.add_incomplete(stack, &acc, &to_add);
    //     // }

    //     let mut acc = None;

    //     let number_of_windows = div_ceil!(C::Scalar::NUM_BITS as usize, window_size);
    //     for i in 0..number_of_windows {
    //         for _ in 0..window_size {
    //             // acc = self.double_incomplete(stack, &acc);
    //             if let Some(_acc) = acc {
    //                 acc = Some(self.double_incomplete(stack, &_acc));
    //             }
    //         }

    //         let mut chain = Vec::with_capacity(tables.len() + 1);
    //         if let Some(acc) = acc {
    //             chain.push(acc)
    //         }

    //         for (table, windowed) in tables.iter().zip(scalars.iter()) {
    //             let selector = &windowed[i];
    //             let to_add = self.select_multi(stack, selector, table);
    //             chain.push(to_add);

    //             // acc = self.add_incomplete(stack, &acc, &to_add);
    //         }
    //         acc = Some(self.add_multi(stack, &chain[..]));
    //     }

    //     self.add_incomplete(stack, &acc.unwrap(), &correction)
    // }
}
