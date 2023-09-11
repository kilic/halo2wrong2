// use crate::Point;
// use halo2_pse::halo2curves::CurveAffine;

// use super::BaseFieldEccChip;

// #[derive(Clone, Debug)]
// pub struct MulFixContext<C: CurveAffine, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize> {
//     window: usize,
//     table: Vec<Vec<Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>>>,
//     correction: Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
// }

// impl<
//         C: CurveAffine,
//         const NUMBER_OF_LIMBS: usize,
//         const LIMB_SIZE: usize,
//         const NUMBER_OF_SUBLIMBS: usize,
//         const SUBLIMB_SIZE: usize,
//     > BaseFieldEccChip<C, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>
// {
//     // pub fn mul_fix(
//     //     &mut self,

//     //     stack: &mut impl ArithmeticChip<C::Scalar>,

//     //     ctx: &MulFixContext<C, NUMBER_OF_LIMBS, LIMB_SIZE>,
//     //     scalar: &Witness<C::Scalar>,
//     // ) -> Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
//     //     let scalar = stack.decompose_generic(scalar, C::Scalar::NUM_BITS as usize, 1);

//     //     let acc: Option<Point<C::Base, C::ScalarExt, NUMBER_OF_LIMBS, LIMB_SIZE>> = scalar
//     //         .chunks(ctx.window)
//     //         .zip(ctx.table.iter())
//     //         .fold(None, |acc, (slice, table)| {
//     //             let acc: Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> = match acc {
//     //                 Some(acc) => {
//     //                     let selected = self.select_multi(stack, slice, &table[..]);
//     //                     self.add_incomplete(stack, &acc, &selected)
//     //                 }
//     //                 None => self.select_multi(stack, slice, &table[..]),
//     //             };
//     //             Some(acc)
//     //         });
//     //     let acc = acc.unwrap();
//     //     unimplemented!()
//     // }
// }
