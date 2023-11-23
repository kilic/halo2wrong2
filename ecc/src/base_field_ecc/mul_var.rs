use circuitry::{
    chip::{
        first_degree::FirstDegreeChip, range::RangeChip, second_degree::SecondDegreeChip,
        select::SelectChip, ROMChip,
    },
    witness::{Composable, Witness},
};
use ff::{Field, PrimeField};
use halo2::halo2curves::CurveAffine;
use std::{ops::Deref, vec};

macro_rules! div_ceil {
    ($a:expr, $b:expr) => {
        (($a - 1) / $b) + 1
    };
}

use crate::Point;

use super::BaseFieldEccChip;

impl<
        C: CurveAffine,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    > BaseFieldEccChip<C, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>
{
    pub fn msm_sliding_vertical<
        Stack: SecondDegreeChip<C::Scalar>
            + FirstDegreeChip<C::Scalar>
            + SelectChip<C::Scalar>
            + RangeChip<C::Scalar>,
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

        let mut round_aux = self.assign_point(stack, self.aux_generator);
        let mut round_aux_acc = None;

        let tables = points
            .chunks(window_size)
            .enumerate()
            .map(|(_, chunk)| {
                let mut table = vec![round_aux.clone()];
                for (i, point) in chunk.iter().enumerate() {
                    for j in 0..(1 << i) {
                        table.push(self.add_incomplete(stack, &table[j], point));
                    }
                }

                // update round aux
                round_aux_acc = if let Some(round_aux_acc) = &round_aux_acc {
                    Some(self.add_incomplete(stack, &round_aux, round_aux_acc))
                } else {
                    Some(round_aux.clone())
                };
                round_aux = self.double_incomplete(stack, &round_aux);

                table
            })
            .collect::<Vec<_>>();

        let round_aux_acc = round_aux_acc.unwrap();
        let mut correction = round_aux_acc.clone();
        for _ in 1..(C::Scalar::NUM_BITS as usize) {
            // TODO: use ladder
            correction = self.double_incomplete(stack, &correction);
            correction = self.add_incomplete(stack, &correction, &round_aux_acc);
        }

        let scalars = scalars
            .iter()
            .map(|scalar| {
                let (_scalar, mut bits) =
                    stack.decompose(scalar.value(), C::Scalar::NUM_BITS as usize, 1);
                stack.equal(&_scalar, scalar);
                bits.reverse();
                bits
            })
            .collect::<Vec<_>>();

        let mut acc = None;

        for round in 0..(C::Scalar::NUM_BITS as usize) {
            let mut chain = Vec::with_capacity(tables.len() + 1);

            if let Some(acc) = acc.as_mut() {
                *acc = self.double_incomplete(stack, acc);
                chain.push(acc.deref().clone());
            }

            for (table, scalars) in tables.iter().zip(scalars.chunks(window_size)) {
                assert_eq!(table.len(), 1 << scalars.len());

                let selector = scalars
                    .iter()
                    .map(|scalar| scalar[round])
                    .collect::<Vec<_>>();

                chain.push(self.select_multi(stack, &selector, table));
            }
            acc = Some(self.add_multi(stack, &chain[..]));
        }

        self.sub_incomplete(stack, &acc.unwrap(), &correction)
    }

    pub fn msm_sliding_vertical_rom<
        Stack: SecondDegreeChip<C::Scalar>
            + FirstDegreeChip<C::Scalar>
            + ROMChip<C::Scalar, NUMBER_OF_LIMBS>
            + RangeChip<C::Scalar>,
    >(
        &self,
        stack: &mut Stack,
        tag: C::Scalar,
        points: &[Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>],
        scalars: &[Witness<C::Scalar>],
        window_size: usize,
    ) -> Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let number_of_points = points.len();
        assert!(number_of_points > 0);
        assert_eq!(number_of_points, scalars.len());
        let table_size = (1 << window_size) as usize;

        let mut round_aux = self.assign_point(stack, self.aux_generator);
        let mut round_aux_acc = None;

        points
            .chunks(window_size)
            .enumerate()
            .for_each(|(chunk_idx, chunk)| {
                let address_base_chunk = C::Scalar::from((2 * chunk_idx * table_size) as u64);

                let mut table = vec![round_aux.clone()];
                self.write_rom(
                    stack,
                    tag,
                    address_base_chunk,
                    table_size,
                    table.last().unwrap(),
                );

                for (i, point) in chunk.iter().enumerate() {
                    for j in 0..(1 << i) {
                        let address_base =
                            C::Scalar::from(((1 << i) + j) as u64) + address_base_chunk;
                        table.push(self.add_incomplete(stack, &table[j], point));
                        self.write_rom(stack, tag, address_base, table_size, table.last().unwrap());
                    }
                }

                // update round aux
                round_aux_acc = if let Some(acc_round_aux) = &round_aux_acc {
                    Some(self.add_incomplete(stack, &round_aux, acc_round_aux))
                } else {
                    Some(round_aux.clone())
                };
                round_aux = self.double_incomplete(stack, &round_aux);
            });

        let round_aux_acc = round_aux_acc.unwrap();
        let mut correction = round_aux_acc.clone();
        for _ in 1..(C::Scalar::NUM_BITS as usize) {
            // TODO: use ladder
            correction = self.double_incomplete(stack, &correction);
            correction = self.add_incomplete(stack, &correction, &round_aux_acc);
        }

        let scalars = scalars
            .iter()
            .map(|scalar| {
                let (_scalar, mut bits) =
                    stack.decompose(scalar.value(), C::Scalar::NUM_BITS as usize, 1);
                stack.equal(&_scalar, scalar);
                bits.reverse();
                bits
            })
            .collect::<Vec<_>>();

        let mut acc = None;

        for round in 0..(C::Scalar::NUM_BITS as usize) {
            let mut chain = Vec::with_capacity(table_size + 1);

            if let Some(acc) = acc.as_mut() {
                *acc = self.double_incomplete(stack, acc);
                chain.push(acc.deref().clone());
            };

            for (chunk_idx, scalars) in scalars.chunks(window_size).enumerate() {
                let selector = scalars
                    .iter()
                    .map(|scalar| scalar[round])
                    .collect::<Vec<_>>();
                let mut base = C::Scalar::ONE;
                let selector = selector
                    .iter()
                    .map(|bit| {
                        let scaled = bit.scale(base);
                        base = base + base;
                        scaled
                    })
                    .collect::<Vec<_>>();

                let address_base = C::Scalar::from((2 * chunk_idx * table_size) as u64);
                let address_fraction = &stack.compose(&selector[..], C::Scalar::ZERO);

                chain.push(self.read_rom(stack, tag, address_base, address_fraction, table_size));
            }
            acc = Some(self.add_multi(stack, &chain[..]));
        }

        self.sub_incomplete(stack, &acc.unwrap(), &correction)
    }

    pub fn msm_sliding_horizontal<
        Stack: SecondDegreeChip<C::Scalar>
            + FirstDegreeChip<C::Scalar>
            + SelectChip<C::Scalar>
            + RangeChip<C::Scalar>,
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

        let number_of_rounds = div_ceil!(C::Scalar::NUM_BITS as usize, window_size);
        let table_size = 1 << window_size;

        let mut aux_pow2 = self.assign_point(stack, self.aux_generator);
        let mut aux_round_acc = aux_pow2.clone();
        let tables: Vec<Vec<Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>>> = points
            .iter()
            .enumerate()
            .map(|(i, point)| {
                let mut table = vec![aux_pow2.clone()];
                for i in 0..(table_size - 1) {
                    table.push(self.add_incomplete(stack, &table[i], point));
                }

                if i != number_of_points - 1 {
                    aux_pow2 = self.double_incomplete(stack, &aux_pow2);
                    aux_round_acc = self.add_incomplete(stack, &aux_round_acc, &aux_pow2);
                }
                table
            })
            .collect();

        let mut correction = aux_round_acc.clone();
        for _ in 1..number_of_rounds {
            for _ in 0..window_size {
                correction = self.double_incomplete(stack, &correction);
            }
            correction = self.add_incomplete(stack, &correction, &aux_round_acc);
        }

        let scalars =
            scalars
                .iter()
                .map(|scalar| {
                    let (_scalar, bits) =
                        stack.decompose(scalar.value(), C::Scalar::NUM_BITS as usize, 1);

                    stack.equal(&_scalar, scalar);

                    bits.chunks(window_size)
                        .rev()
                        .map(|chunk| chunk.to_vec())
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();

        let mut acc = None;
        for i in 0..number_of_rounds {
            for _ in 0..window_size {
                if let Some(_acc) = acc {
                    acc = Some(self.double_incomplete(stack, &_acc));
                }
            }

            let mut chain = Vec::with_capacity(tables.len() + 1);
            if let Some(acc) = acc {
                chain.push(acc)
            }

            for (table, windowed) in tables.iter().zip(scalars.iter()) {
                let selector = &windowed[i];
                let to_add = self.select_multi(stack, selector, table);
                chain.push(to_add);
            }
            acc = Some(self.add_multi(stack, &chain[..]));
        }

        self.sub_incomplete(stack, &acc.unwrap(), &correction)
    }

    pub fn msm_sliding_horizontal_rom<
        Stack: SecondDegreeChip<C::Scalar>
            + FirstDegreeChip<C::Scalar>
            + ROMChip<C::Scalar, NUMBER_OF_LIMBS>
            + RangeChip<C::Scalar>,
    >(
        &self,
        stack: &mut Stack,
        tag: C::Scalar,
        points: &[Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>],
        scalars: &[Witness<C::Scalar>],
        window_size: usize,
    ) -> Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let number_of_points = points.len();
        assert!(number_of_points > 0);
        assert_eq!(number_of_points, scalars.len());

        let number_of_rounds = div_ceil!(C::Scalar::NUM_BITS as usize, window_size);
        let table_size = 1 << window_size;

        let mut aux_pow2 = self.assign_point(stack, self.aux_generator);
        let mut aux_round_acc = aux_pow2.clone();

        points.iter().enumerate().for_each(|(point_idx, point)| {
            let address_base = C::Scalar::from((2 * table_size * point_idx) as u64);
            let mut prev = aux_pow2.clone();

            self.write_rom(stack, tag, address_base, table_size, &prev);

            // let mut table = vec![aux_pow2.clone()];
            for table_idx in 1..table_size {
                prev = self.add_incomplete(stack, &prev, point);

                self.write_rom(
                    stack,
                    tag,
                    address_base + C::Scalar::from(table_idx as u64),
                    table_size,
                    &prev,
                );
            }

            if point_idx != number_of_points - 1 {
                aux_pow2 = self.double_incomplete(stack, &aux_pow2);
                aux_round_acc = self.add_incomplete(stack, &aux_round_acc, &aux_pow2);
            }
        });

        let mut correction = aux_round_acc.clone();
        for _ in 1..number_of_rounds {
            for _ in 0..window_size {
                correction = self.double_incomplete(stack, &correction);
            }
            correction = self.add_incomplete(stack, &correction, &aux_round_acc);
        }

        let scalars = scalars
            .iter()
            .map(|scalar| {
                let (_scalar, mut limbs) =
                    stack.decompose(scalar.value(), C::Scalar::NUM_BITS as usize, window_size);

                stack.equal(&_scalar, scalar);

                limbs.reverse();
                limbs
            })
            .collect::<Vec<_>>();

        let mut acc = None;
        for i in 0..number_of_rounds {
            for _ in 0..window_size {
                if let Some(_acc) = acc {
                    acc = Some(self.double_incomplete(stack, &_acc));
                }
            }

            let mut chain = Vec::with_capacity(table_size + 1);

            if let Some(acc) = acc {
                chain.push(acc)
            }

            for (point_idx, scalar) in scalars.iter().enumerate() {
                let selector = &scalar[i];
                let address_base = C::Scalar::from((2 * table_size * point_idx) as u64);
                let to_add = self.read_rom(stack, tag, address_base, selector, table_size);
                chain.push(to_add);
            }
            acc = Some(self.add_multi(stack, &chain[..]));
        }

        self.sub_incomplete(stack, &acc.unwrap(), &correction)
    }
}
