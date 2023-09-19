// use std::collections::{BTreeMap, BTreeSet};

// use ff::PrimeField;
// use halo2::{
//     circuit::{Layouter, Value},
//     plonk::Error,
// };

// use circuitry::{
//     chip::{first_degree::FirstDegreeChip, select::SelectChip, Chip, Core},
//     enforcement::{CRT256Enforcement, ConstantEquality, FirstDegreeComposition, Selection},
//     gates::{
//         range::{range_sizes, RangeTableLayout},
//         GateLayout,
//     },
//     witness::Witness,
//     LayoutCtx, RegionCtx,
// };

// use crate::chip::CRT256Chip;

// #[derive(Clone, Debug, Default)]
// pub struct Stack<F: PrimeField + Ord, const NUMBER_OF_LIMBS: usize> {
//     // to give uniques id to witnesses
//     pub(crate) number_of_witnesses: u32,
//     // store registred constants
//     pub(crate) constants: BTreeMap<F, Witness<F>>,
//     // store arbitrary binary decomposition bases
//     pub(crate) pow_of_twos: BTreeMap<usize, Vec<F>>,
//     // indirect copies
//     pub(crate) copies: Vec<(u32, u32)>,
//     // ranged witnesses
//     pub(crate) ranges: Vec<Witness<F>>,
//     // final fixed tables
//     pub(crate) range_tables: BTreeSet<usize>,
//     // composition enforcements to be layouted
//     pub(crate) first_degree_compositions: Vec<FirstDegreeComposition<F>>,
//     // constant registries
//     pub(crate) constant_equalities: Vec<ConstantEquality<F>>,
//     // composition enforcements to be layouted
//     pub(crate) selections: Vec<Selection<F>>,
//     //
//     pub(crate) crts: Vec<CRT256Enforcement<F, NUMBER_OF_LIMBS>>,
// }

// // Essentias
// impl<F: PrimeField + Ord, const NUMBER_OF_LIMBS: usize> Core<F> for Stack<F, NUMBER_OF_LIMBS> {
//     fn new_witness(&mut self, value: Value<F>) -> Witness<F> {
//         self.number_of_witnesses += 1;
//         Witness::new(self.number_of_witnesses, value)
//     }

//     fn new_witness_in_range(&mut self, value: Value<F>, bit_size: usize) -> Witness<F> {
//         self.number_of_witnesses += 1;
//         let witness = Witness::new_in_range(self.number_of_witnesses, value, bit_size);
//         self.ranges.push(witness);
//         self.range_tables.insert(bit_size);
//         witness
//     }

//     fn equal(&mut self, w0: &Witness<F>, w1: &Witness<F>) {
//         match (w0.id(), w1.id()) {
//             (Some(id0), Some(id1)) => {
//                 self.copies.push((id0, id1));
//             }
//             _ => panic!("cannot copy tmp witness"),
//         }
//     }

//     fn get_constant(&mut self, constant: F) -> Witness<F> {
//         match self.constants.get(&constant) {
//             Some(constant) => *constant,
//             _ => {
//                 let w = self.new_witness(Value::known(constant));
//                 self.equal_to_constant(&w, constant);
//                 assert!(self.constants.insert(constant, w).is_none());
//                 w
//             }
//         }
//     }
// }

// impl<F: PrimeField + Ord, const NUMBER_OF_LIMBS: usize> Stack<F, NUMBER_OF_LIMBS> {
//     pub fn equal_to_constant(&mut self, w0: &Witness<F>, constant: F) {
//         self.constant_equalities
//             .push(ConstantEquality::new(w0.clone(), constant));
//     }

//     pub fn layout_first_degree_compositions<
//         L: Layouter<F>,
//         Gate: GateLayout<F, Vec<FirstDegreeComposition<F>>>,
//     >(
//         &mut self,
//         ly: &mut LayoutCtx<F, L>,
//         gate: &Gate,
//     ) -> Result<(), Error> {
//         let e = std::mem::take(&mut self.first_degree_compositions);
//         gate.layout(ly, e)?;
//         Ok(())
//     }

//     pub fn layout_selects<L: Layouter<F>, Gate: GateLayout<F, Vec<Selection<F>>>>(
//         &mut self,
//         ly: &mut LayoutCtx<F, L>,
//         gate: &Gate,
//     ) -> Result<(), Error> {
//         let e = std::mem::take(&mut self.selections);
//         gate.layout(ly, e)?;
//         Ok(())
//     }

//     pub fn layout_crts<
//         L: Layouter<F>,
//         Gate: GateLayout<F, Vec<CRT256Enforcement<F, NUMBER_OF_LIMBS>>>,
//     >(
//         &mut self,
//         ly: &mut LayoutCtx<F, L>,
//         gate: &Gate,
//     ) -> Result<(), Error> {
//         let e = std::mem::take(&mut self.crts);
//         gate.layout(ly, e)?;
//         Ok(())
//     }

//     pub fn layout_range_tables<L: Layouter<F>, Gate: RangeTableLayout<F>>(
//         &mut self,
//         ly: &mut LayoutCtx<F, L>,
//         gate: &Gate,
//     ) -> Result<(), Error> {
//         let mut tables: Vec<_> = self.range_tables.iter().copied().collect();
//         tables.sort();
//         #[cfg(feature = "synth-sanity")]
//         {
//             assert_eq!(range_sizes(&self.ranges[..]), tables);
//         }
//         gate.layout_range_tables(ly, &tables)
//     }

//     pub fn apply_indirect_copies<L: Layouter<F>>(
//         &mut self,
//         ly: &mut LayoutCtx<F, L>,
//     ) -> Result<(), Error> {
//         ly.layouter.assign_region(
//             || "",
//             |region| {
//                 let ctx = &mut RegionCtx::new(region, &mut ly.cell_map);

//                 for (id0, id1) in self.copies.iter() {
//                     ctx.copy(*id0, *id1)?;
//                 }

//                 Ok(())
//             },
//         )
//     }
// }

// impl<F: PrimeField + Ord, const NUMBER_OF_LIMBS: usize> Chip<FirstDegreeComposition<F>, F>
//     for Stack<F, NUMBER_OF_LIMBS>
// {
//     fn new_op(&mut self, e: FirstDegreeComposition<F>) {
//         self.first_degree_compositions.push(e);
//     }
// }

// impl<F: PrimeField + Ord, const NUMBER_OF_LIMBS: usize> Chip<Selection<F>, F>
//     for Stack<F, NUMBER_OF_LIMBS>
// {
//     fn new_op(&mut self, e: Selection<F>) {
//         self.selections.push(e);
//     }
// }

// impl<F: PrimeField + Ord, const NUMBER_OF_LIMBS: usize>
//     Chip<CRT256Enforcement<F, NUMBER_OF_LIMBS>, F> for Stack<F, NUMBER_OF_LIMBS>
// {
//     fn new_op(&mut self, e: CRT256Enforcement<F, NUMBER_OF_LIMBS>) {
//         self.crts.push(e);
//     }
// }

// impl<F: PrimeField + Ord, const NUMBER_OF_LIMBS: usize> SelectChip<F>
//     for Stack<F, NUMBER_OF_LIMBS>
// {
// }

// impl<F: PrimeField + Ord, const NUMBER_OF_LIMBS: usize> CRT256Chip<F, NUMBER_OF_LIMBS>
//     for Stack<F, NUMBER_OF_LIMBS>
// {
// }

// impl<F: PrimeField + Ord, const NUMBER_OF_LIMBS: usize> FirstDegreeChip<F>
//     for Stack<F, NUMBER_OF_LIMBS>
// {
// }

// // impl<F: PrimeField + Ord> Stack<F,NUMBER_OF_LIMBS> {
// //     fn equal_to_constant(&mut self, w0: &Witness<F>, constant: F) {
// //         self.constant_equalities
// //             .push(ConstantEquality::new(w0.clone(), constant));
// //     }

// //     pub fn zero_sum(&mut self, terms: &[Scaled<F>], constant_to_add: F) {
// //         let terms: Vec<Scaled<F>> = terms.iter().filter(|e| !e.is_empty()).cloned().collect();

// //         assert!(!terms.is_empty());

// //         #[cfg(feature = "prover-sanity")]
// //         {
// //             let result = Scaled::compose(&terms[..], constant_to_add);
// //             result.map(|must_be_zero| {
// //                 debug_assert_eq!(must_be_zero, F::zero());
// //             });
// //         }

// //         let composition = FirstDegreeComposition::new(terms, constant_to_add);
// //         self.first_degree_compositions.push(composition);
// //     }

// //     pub fn compose(&mut self, terms: &[Scaled<F>], constant_to_add: F) -> Witness<F> {
// //         let mut terms: Vec<Scaled<F>> = terms.iter().filter(|e| !e.is_empty()).cloned().collect();
// //         assert!(!terms.is_empty());
// //         let result = Scaled::compose(&terms[..], constant_to_add);
// //         let result = self.new_witness(result).sub();
// //         terms.push(result);
// //         let composition = FirstDegreeComposition::new(terms, constant_to_add);
// //         self.first_degree_compositions.push(composition);
// //         result.witness
// //     }
// // }
