// use std::marker::PhantomData;

// use crate::{
//     enforcement::CRT256Enforcement,
//     utils::{big_to_fe, big_to_fe_unsafe, decompose, modulus},
//     witness::{Composable, Witness},
//     LayoutCtx, RegionCtx,
// };
// use ff::PrimeField;
// use halo2::{
//     circuit::Layouter,
//     plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Expression, Selector},
//     poly::Rotation,
// };
// use num_bigint::BigUint;
// use num_traits::One;

// use super::GateLayout;

// #[derive(Debug, Clone)]
// pub struct CRTGate<
//     W: PrimeField,
//     N: PrimeField,
//     const NUMBER_OF_LIMBS: usize,
//     const LIMB_SIZE: usize,
// > {
//     pub(super) advice: [Column<Advice>; NUMBER_OF_LIMBS],
//     pub(super) mul_selector: Selector,
//     pub(super) red_selector: Selector,
//     _marker: PhantomData<(W, N)>,
// }

// impl<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>
//     CRTGate<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>
// {
//     pub fn new(
//         meta: &mut ConstraintSystem<N>,
//         advice: &[Column<Advice>; NUMBER_OF_LIMBS],
//     ) -> CRTGate<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
//         let mul_selector = meta.selector();
//         let red_selector = meta.selector();
//         Self {
//             advice: advice.clone(),
//             mul_selector,
//             red_selector,
//             _marker: PhantomData,
//         }
//     }

//     pub fn configure(&self, meta: &mut ConstraintSystem<N>) {
//         let two = N::ONE + N::ONE;
//         let base = two.pow([(LIMB_SIZE) as u64]);

//         let binary_modulus = &(BigUint::one() << (LIMB_SIZE * NUMBER_OF_LIMBS));
//         let wrong_modulus = &modulus::<W>();
//         let negative_wrong_modulus_decomposed =
//             decompose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&(binary_modulus - wrong_modulus));
//         let negative_wrong_modulus_decomposed: [N; NUMBER_OF_LIMBS] =
//             negative_wrong_modulus_decomposed
//                 .iter()
//                 .map(big_to_fe_unsafe)
//                 .collect::<Vec<_>>()
//                 .try_into()
//                 .unwrap();

//         let native_modulus = &modulus::<N>();
//         let wrong_modulus_in_native_modulus: N = big_to_fe(&(wrong_modulus % native_modulus));

//         let nat = |limbs: Vec<Expression<N>>| -> Expression<N> {
//             limbs
//                 .into_iter()
//                 .enumerate()
//                 .fold(Expression::Constant(N::ZERO), |acc, (i, limb)| {
//                     acc + limb * base.pow(&[i as u64])
//                 })
//         };

//         meta.create_gate("mul", |meta| {
//             // should work with division and squaring

//             let w0 = self
//                 .advice
//                 .iter()
//                 .map(|col| meta.query_advice(*col, Rotation(0)))
//                 .collect::<Vec<_>>();

//             let w1 = self
//                 .advice
//                 .iter()
//                 .map(|col| meta.query_advice(*col, Rotation(1)))
//                 .collect::<Vec<_>>();

//             let result = self
//                 .advice
//                 .iter()
//                 .map(|col| meta.query_advice(*col, Rotation(2)))
//                 .collect::<Vec<_>>();

//             let quotient = self
//                 .advice
//                 .iter()
//                 .map(|col| meta.query_advice(*col, Rotation(3)))
//                 .collect::<Vec<_>>();

//             let carry = self
//                 .advice
//                 .iter()
//                 .map(|col| meta.query_advice(*col, Rotation(4)))
//                 .collect::<Vec<_>>();

//             let to_sub = self
//                 .advice
//                 .iter()
//                 .map(|col| meta.query_advice(*col, Rotation(5)))
//                 .collect::<Vec<_>>();

//             let t = result
//                 .clone()
//                 .into_iter()
//                 .zip(to_sub.clone().into_iter())
//                 .enumerate()
//                 .map(|(i, (result, to_sub))| {
//                     let t = w0
//                         .clone()
//                         .into_iter()
//                         .take(i + 1)
//                         .zip(w1.clone().into_iter().take(i + 1).rev())
//                         .fold(-result + to_sub, |acc, (w0, w1)| acc + w0 * w1);

//                     let t = quotient
//                         .clone()
//                         .into_iter()
//                         .take(i + 1)
//                         .zip(negative_wrong_modulus_decomposed.iter().take(i + 1).rev())
//                         .fold(t, |acc, (quotient, modulus)| acc + quotient * *modulus);

//                     t
//                 })
//                 .collect::<Vec<_>>();

//             let mut prev: Option<Expression<N>> = None;
//             let carry_gates = t
//                 .into_iter()
//                 .zip(carry.into_iter())
//                 .enumerate()
//                 .map(|(_, (t, carry))| {
//                     let expr = t - carry.clone() * base;
//                     let expr = if let Some(prev) = &prev {
//                         expr + prev.clone()
//                     } else {
//                         expr
//                     };
//                     prev = Some(carry);
//                     expr
//                 })
//                 .collect::<Vec<_>>();

//             let w0_nat = nat(w0);
//             let w1_nat = nat(w1);
//             let quotient_nat = nat(quotient);
//             let result_nat = nat(result);
//             let native_gate =
//                 w0_nat * w1_nat - quotient_nat * wrong_modulus_in_native_modulus - result_nat;

//             let selector = meta.query_selector(self.mul_selector);
//             Constraints::with_selector(
//                 selector,
//                 carry_gates.into_iter().chain(std::iter::once(native_gate)),
//             )
//         });

//         meta.create_gate("reduce small", |meta| {
//             let w0 = self
//                 .advice
//                 .iter()
//                 .map(|col| meta.query_advice(*col, Rotation(0)))
//                 .collect::<Vec<_>>();

//             let result = self
//                 .advice
//                 .iter()
//                 .map(|col| meta.query_advice(*col, Rotation(1)))
//                 .collect::<Vec<_>>();

//             let carry = self
//                 .advice
//                 .iter()
//                 .map(|col| meta.query_advice(*col, Rotation(2)))
//                 .collect::<Vec<_>>();

//             let quotient = meta.query_advice(*self.advice.first().unwrap(), Rotation(3));

//             let t = result
//                 .clone()
//                 .into_iter()
//                 .zip(w0.clone().into_iter())
//                 .zip(negative_wrong_modulus_decomposed.into_iter())
//                 .enumerate()
//                 .map(|(_, ((result, w0), p))| w0 - result + quotient.clone() * p)
//                 .collect::<Vec<_>>();

//             let mut prev: Option<Expression<N>> = None;
//             let carry_gates = t
//                 .into_iter()
//                 .zip(carry.into_iter())
//                 .enumerate()
//                 .map(|(_, (t, carry))| {
//                     let expr = t - carry.clone() * base;
//                     let expr = if let Some(prev) = &prev {
//                         expr + prev.clone()
//                     } else {
//                         expr
//                     };
//                     prev = Some(carry);
//                     expr
//                 })
//                 .collect::<Vec<_>>();

//             let w0_nat = nat(w0);
//             let result_nat = nat(result);
//             let native_gate = w0_nat - quotient * wrong_modulus_in_native_modulus - result_nat;

//             let selector = meta.query_selector(self.red_selector);
//             Constraints::with_selector(
//                 selector,
//                 carry_gates.into_iter().chain(std::iter::once(native_gate)),
//             )
//         });
//     }
// }

// impl<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>
//     CRTGate<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>
// {
//     pub fn mul(
//         &self,
//         ctx: &mut RegionCtx<'_, '_, N>,
//         w0: &[Witness<N>; NUMBER_OF_LIMBS],
//         w1: &[Witness<N>; NUMBER_OF_LIMBS],
//         result: &[Witness<N>; NUMBER_OF_LIMBS],
//         quotient: &[Witness<N>; NUMBER_OF_LIMBS],
//         carries: &[Witness<N>; NUMBER_OF_LIMBS],
//         to_sub: &[Witness<N>; NUMBER_OF_LIMBS],
//     ) -> Result<(), Error> {
//         ctx.enable(self.mul_selector)?;

//         let _ = w0
//             .iter()
//             .zip(self.advice.into_iter())
//             .map(|(limb, column)| ctx.advice(column, limb.value()))
//             .collect::<Result<Vec<_>, Error>>()?;
//         ctx.next();

//         let _ = w1
//             .iter()
//             .zip(self.advice.into_iter())
//             .map(|(limb, column)| ctx.advice(column, limb.value()))
//             .collect::<Result<Vec<_>, Error>>()?;
//         ctx.next();

//         let _ = result
//             .iter()
//             .zip(self.advice.into_iter())
//             .map(|(limb, column)| ctx.advice(column, limb.value()))
//             .collect::<Result<Vec<_>, Error>>()?;
//         ctx.next();

//         let _ = quotient
//             .iter()
//             .zip(self.advice.into_iter())
//             .map(|(limb, column)| ctx.advice(column, limb.value()))
//             .collect::<Result<Vec<_>, Error>>()?;
//         ctx.next();

//         let _ = carries
//             .iter()
//             .zip(self.advice.into_iter())
//             .map(|(limb, column)| ctx.advice(column, limb.value()))
//             .collect::<Result<Vec<_>, Error>>()?;
//         ctx.next();

//         let _ = to_sub
//             .iter()
//             .zip(self.advice.into_iter())
//             .map(|(limb, column)| ctx.advice(column, limb.value()))
//             .collect::<Result<Vec<_>, Error>>()?;

//         ctx.next();

//         Ok(())
//     }

//     pub fn reduce(
//         &self,
//         ctx: &mut RegionCtx<'_, '_, N>,
//         w0: &[Witness<N>; NUMBER_OF_LIMBS],
//         result: &[Witness<N>; NUMBER_OF_LIMBS],
//         carries: &[Witness<N>; NUMBER_OF_LIMBS],
//         quotient: &Witness<N>,
//     ) -> Result<(), Error> {
//         ctx.enable(self.red_selector)?;

//         let _ = w0
//             .iter()
//             .zip(self.advice.into_iter())
//             .map(|(limb, column)| ctx.advice(column, limb.value()))
//             .collect::<Result<Vec<_>, Error>>()?;
//         ctx.next();

//         let _ = result
//             .iter()
//             .zip(self.advice.into_iter())
//             .map(|(limb, column)| ctx.advice(column, limb.value()))
//             .collect::<Result<Vec<_>, Error>>()?;
//         ctx.next();

//         let _ = carries
//             .iter()
//             .zip(self.advice.into_iter())
//             .map(|(limb, column)| ctx.advice(column, limb.value()))
//             .collect::<Result<Vec<_>, Error>>()?;
//         ctx.next();

//         ctx.advice(*self.advice.first().unwrap(), quotient.value())?;
//         ctx.next();

//         Ok(())
//     }
// }

// impl<W: PrimeField, N: PrimeField + Ord, const NUMBER_OF_LIMGS: usize, const LIMB_SIZE: usize>
//     GateLayout<N, &[CRT256Enforcement<N, NUMBER_OF_LIMGS>]>
//     for CRTGate<W, N, NUMBER_OF_LIMGS, LIMB_SIZE>
// {
//     fn layout<L: Layouter<N>>(
//         &self,
//         ly_ctx: &mut LayoutCtx<N, L>,
//         e: &[CRT256Enforcement<N, NUMBER_OF_LIMGS>],
//     ) -> Result<(), Error> {
//         let _offset = ly_ctx.layouter.assign_region(
//             || "",
//             |region| {
//                 let ctx = &mut crate::RegionCtx::new(region, &mut ly_ctx.cell_map);

//                 for e in e.iter() {
//                     match e {
//                         CRT256Enforcement::Mul {
//                             w0,
//                             w1,
//                             result,
//                             quotient,
//                             carries,
//                             to_sub,
//                         } => self.mul(ctx, w0, w1, result, quotient, carries, to_sub)?,
//                         CRT256Enforcement::Reduce {
//                             w0,
//                             result,
//                             carries,
//                             quotient,
//                         } => self.reduce(ctx, w0, result, carries, quotient)?,
//                     }
//                 }
//                 Ok(ctx.offset())
//             },
//         )?;

//         {
//             println!("---");
//             println!("* crt constraints: {}", _offset);
//             let mul = e
//                 .iter()
//                 .filter(|x| match x {
//                     CRT256Enforcement::Mul {
//                         w0: _,
//                         w1: _,
//                         result: _,
//                         quotient: _,
//                         carries: _,
//                         to_sub: _,
//                     } => true,
//                     _ => false,
//                 })
//                 .count();

//             let red = e
//                 .iter()
//                 .filter(|x| match x {
//                     CRT256Enforcement::Reduce {
//                         w0: _,
//                         result: _,
//                         quotient: _,
//                         carries: _,
//                     } => true,
//                     _ => false,
//                 })
//                 .count();

//             println!("* * mul: {mul}");
//             println!("* * red: {red}");
//             println!("* * rows: {}", _offset);
//             println!();
//         }

//         Ok(())
//     }
// }
