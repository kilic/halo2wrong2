use super::GateLayout;
use crate::{
    enforcement::{FirstDegreeComposition, SecondDegreeComposition, Selection},
    witness::{Composable, Scaled, SecondDegreeScaled, Term, Witness},
    LayoutCtx, RegionCtx,
};
use ff::PrimeField;
use halo2_pse::{
    circuit::{Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Fixed, Selector},
    poly::Rotation,
};
use std::{collections::BTreeMap, marker::PhantomData};

pub enum ColumnID {
    A,
    B,
    C,
}

impl ColumnID {
    pub fn index(&self) -> usize {
        match self {
            Self::A => 0,
            Self::B => 1,
            Self::C => 2,
        }
    }
}

#[derive(Clone, Debug)]
pub struct VanillaGate<F: PrimeField> {
    pub(crate) selector: Selector,
    pub(crate) s_mul: Column<Fixed>,

    pub(crate) a: Column<Advice>,
    pub(crate) b: Column<Advice>,
    pub(crate) c: Column<Advice>,

    pub(crate) sa: Column<Fixed>,
    pub(crate) sb: Column<Fixed>,
    pub(crate) sc: Column<Fixed>,
    pub(crate) s_next: Option<Column<Fixed>>,
    pub(crate) constant: Option<Column<Fixed>>,
    // pub(crate) _public_inputs: Option<Column<Instance>>,
    pub(crate) _marker: PhantomData<F>,
}

impl<F: PrimeField> VanillaGate<F> {
    pub fn advice_colums(&self) -> [Column<Advice>; 3] {
        self.columns_ids()
            .into_iter()
            .map(|id| self.column(&id).1)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    pub fn fixed_columns(&self) -> [Column<Fixed>; 3] {
        self.columns_ids()
            .into_iter()
            .map(|id| self.column(&id).0)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    pub fn constant(&self) -> Column<Fixed> {
        self.constant.unwrap()
    }

    fn columns_ids(&self) -> Vec<ColumnID> {
        vec![ColumnID::A, ColumnID::B, ColumnID::C]
    }

    fn column(&self, id: &ColumnID) -> (Column<Fixed>, Column<Advice>) {
        match id {
            ColumnID::A => (self.sa, self.a),
            ColumnID::B => (self.sb, self.b),
            ColumnID::C => (self.sc, self.c),
        }
    }

    fn enable(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        ctx.enable(self.selector)
    }

    fn next(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        self.enable(ctx)?;
        ctx.next();
        Ok(())
    }

    fn enable_scaled_mul(&self, ctx: &mut RegionCtx<'_, '_, F>, factor: F) -> Result<(), Error> {
        ctx.fixed(self.s_mul, factor).map(|_| ())
    }

    fn enable_scaled_next(&self, ctx: &mut RegionCtx<'_, '_, F>, factor: F) -> Result<(), Error> {
        if let Some(column) = self.s_next {
            ctx.fixed(column, factor).map(|_| ())
        } else {
            Ok(())
        }
    }

    fn disable_next(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        if let Some(column) = self.s_next {
            ctx.fixed(column, F::ZERO).map(|_| ())
        } else {
            Ok(())
        }
    }

    fn set_constant(&self, ctx: &mut RegionCtx<'_, '_, F>, constant: F) -> Result<(), Error> {
        if let Some(column) = self.constant {
            ctx.fixed(column, constant).map(|_| ())
        } else {
            Ok(())
        }
    }

    fn assign(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        column: &ColumnID,
        e: &Scaled<F>,
    ) -> Result<(), Error> {
        // resolve column
        let (fixed, advice) = self.column(column);
        // assign fixed
        ctx.fixed(fixed, e.factor)?;
        // assign witness
        let witness = e.witness;
        let new_cell = ctx.advice(advice, witness.value)?;
        // if already assigned enfoce copy constraint
        // if not add as the root of this witness
        if let Some(id) = witness.id {
            ctx.copy_chain(id, new_cell)?;
        }
        Ok(())
    }

    fn disable_mul(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        self.enable_scaled_mul(ctx, F::ZERO)
    }

    fn disable_constant(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        self.set_constant(ctx, F::ZERO)
    }

    fn enable_mul(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        self.enable_scaled_mul(ctx, F::ONE)
    }

    fn enable_next(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        self.enable_scaled_next(ctx, F::ONE)
    }

    fn no_op(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        self.disable_constant(ctx)?;
        self.disable_mul(ctx)?;
        self.disable_next(ctx)?;
        ctx.empty(self.sa.into())?;
        ctx.empty(self.sb.into())?;
        ctx.empty(self.sc.into())?;
        Ok(())
    }

    fn empty_row(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        self.no_op(ctx)?;
        self.no_witness(ctx)?;
        ctx.next();
        Ok(())
    }

    fn empty_cell(&self, ctx: &mut RegionCtx<'_, '_, F>, column: &ColumnID) -> Result<(), Error> {
        let (fixed, advice) = self.column(column);
        ctx.fixed(fixed, F::ZERO)?;
        ctx.advice(advice, Value::known(F::ZERO))?;
        Ok(())
    }

    fn no_witness(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        for c in self.columns_ids().iter() {
            self.empty_cell(ctx, c)?;
        }
        Ok(())
    }
}

impl<F: PrimeField + Ord> VanillaGate<F> {
    pub fn new(meta: &mut ConstraintSystem<F>) -> Self {
        let selector = meta.selector();
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let sa = meta.fixed_column();
        let sb = meta.fixed_column();
        let sc = meta.fixed_column();
        let s_mul = meta.fixed_column();
        let (s_next, constant) = (meta.fixed_column(), meta.fixed_column());
        // let public_inputs = meta.instance_column();

        Self {
            selector,
            a,
            b,
            c,
            sa,
            sb,
            sc,
            s_mul,
            s_next: Some(s_next),
            constant: Some(constant),
            _marker: PhantomData,
        }
    }

    pub fn configure(&self, meta: &mut ConstraintSystem<F>) {
        meta.enable_equality(self.a);
        meta.enable_equality(self.b);
        meta.enable_equality(self.c);
        meta.create_gate("vanilla gate", |meta| {
            let a = meta.query_advice(self.a, Rotation::cur());
            let b = meta.query_advice(self.b, Rotation::cur());
            let next = meta.query_advice(self.c, Rotation::next());
            let c = meta.query_advice(self.c, Rotation::cur());
            let sa = meta.query_fixed(self.sa, Rotation::cur());
            let sb = meta.query_fixed(self.sb, Rotation::cur());
            let sc = meta.query_fixed(self.sc, Rotation::cur());
            let s_mul = meta.query_fixed(self.s_mul, Rotation::cur());

            let mut expression = a.clone() * sa + b.clone() * sb + c * sc + a * b * s_mul;

            if let Some(constant) = self.constant {
                expression = expression + meta.query_fixed(constant, Rotation::cur());
            }
            if let Some(s_next) = self.s_next {
                let s_next = meta.query_fixed(s_next, Rotation::cur());
                expression = expression + s_next * next;
            }

            let selector = meta.query_selector(self.selector);
            Constraints::with_selector(selector, vec![expression])
        });
    }
}

impl<F: PrimeField + Ord> GateLayout<F, Vec<FirstDegreeComposition<F>>> for VanillaGate<F> {
    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<FirstDegreeComposition<F>>,
    ) -> Result<(), Error> {
        #[cfg(feature = "info")]
        {
            let mut n_first: BTreeMap<usize, usize> = BTreeMap::new();

            for op in e.iter() {
                n_first
                    .entry(op.terms.len())
                    .and_modify(|count| *count += 1)
                    .or_insert_with(|| 1);
            }

            println!("---");
            println!("* number of compositions: {}", e.len());
            for (n_terms, count) in n_first {
                println!("* * zerosum n: {n_terms} occurs: {count}");
            }
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut crate::RegionCtx::new(region, &mut ly_ctx.cell_map);

                for op in e.iter() {
                    self.zero_sum(ctx, &op.terms, op.constant)?;
                }

                self.empty_row(ctx)?;

                Ok(ctx.offset())
            },
        )?;

        #[cfg(feature = "info")]
        {
            println!("* * rows: {}", _offset);
            println!();
        }

        Ok(())
    }
}

impl<F: PrimeField + Ord> GateLayout<F, Vec<SecondDegreeComposition<F>>> for VanillaGate<F> {
    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<SecondDegreeComposition<F>>,
    ) -> Result<(), Error> {
        #[cfg(feature = "info")]
        {
            let mut n_second: BTreeMap<(usize, usize), usize> = BTreeMap::new();

            for op in e.iter() {
                let n_terms1: usize = op
                    .terms
                    .iter()
                    .filter_map(|term| match term {
                        Term::First(_) => Some(()),
                        _ => None,
                    })
                    .count();
                let n_terms2: usize = op
                    .terms
                    .iter()
                    .filter_map(|term| match term {
                        Term::Second(_) => Some(()),
                        _ => None,
                    })
                    .count();
                n_second
                    .entry((n_terms1, n_terms2))
                    .and_modify(|count| *count += 1)
                    .or_insert_with(|| 1);
            }

            for (n_terms, count) in n_second {
                println!(
                    "* * zerosum n: {} nn: {} occurs: {}",
                    n_terms.0, n_terms.1, count
                );
            }
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut crate::RegionCtx::new(region, &mut ly_ctx.cell_map);

                for op in e.iter() {
                    self.zero_sum_second_degree(ctx, &op.terms, op.constant)?;
                }

                self.empty_row(ctx)?;

                Ok(ctx.offset())
            },
        )?;

        #[cfg(feature = "info")]
        {
            println!("* * rows: {}", _offset);
            println!();
        }

        Ok(())
    }
}

impl<F: PrimeField + Ord> GateLayout<F, Vec<Selection<F>>> for VanillaGate<F> {
    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<Selection<F>>,
    ) -> Result<(), Error> {
        #[cfg(feature = "info")]
        {
            println!("---");
            println!("* number of selects: {}", e.len());
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut crate::RegionCtx::new(region, &mut ly_ctx.cell_map);
                for op in e.iter() {
                    self.select(ctx, &op.cond, &op.w0, &op.w1, &op.selected)?;
                }
                self.empty_row(ctx)?;
                Ok(ctx.offset())
            },
        )?;

        #[cfg(feature = "info")]
        {
            println!("* * rows: {}", _offset);
            println!();
        }

        Ok(())
    }
}

impl<F: PrimeField> VanillaGate<F> {
    fn select(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        cond: &Witness<F>,
        w0: &Witness<F>,
        w1: &Witness<F>,
        selected: &Witness<F>,
    ) -> Result<(), Error> {
        // c*w0 - c*w1 + w1 - res = 0
        // * first row
        // -c*w1 + w1 - res = tmp
        // tmp = c * w0
        self.enable_scaled_mul(ctx, -F::ONE)?;
        self.enable_next(ctx)?;
        self.disable_constant(ctx)?;
        Self::assign(self, ctx, &ColumnID::A, &Scaled::add(w1))?;
        Self::assign(self, ctx, &ColumnID::B, &Scaled::mul(cond))?;
        Self::assign(self, ctx, &ColumnID::C, &Scaled::sub(selected))?;
        self.next(ctx)?;
        // * second row
        // c * w0 = -tmp
        // find the temp witenss
        let c_w0 = cond.value() * w0.value();
        let c_w0 = Scaled::tmp(c_w0, -F::ONE);
        self.enable_mul(ctx)?;
        self.disable_next(ctx)?;
        self.disable_constant(ctx)?;
        Self::assign(self, ctx, &ColumnID::A, &Scaled::mul(w0))?;
        Self::assign(self, ctx, &ColumnID::B, &Scaled::mul(cond))?;
        Self::assign(self, ctx, &ColumnID::C, &c_w0)?;
        self.next(ctx)
    }

    fn or(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        w0: &Witness<F>,
        w1: &Witness<F>,
        result: &Witness<F>,
    ) -> Result<(), Error> {
        self.disable_next(ctx)?;
        self.disable_constant(ctx)?;
        self.enable_mul(ctx)?;
        Self::assign(self, ctx, &ColumnID::A, &Scaled::sub(w0))?;
        Self::assign(self, ctx, &ColumnID::B, &Scaled::sub(w1))?;
        Self::assign(self, ctx, &ColumnID::C, &Scaled::add(result))?;
        self.next(ctx)?;
        Ok(())
    }

    fn zero_sum(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        terms: &[Scaled<F>],
        constant: F,
    ) -> Result<(), Error> {
        let mut terms = terms.to_vec();
        let corner = terms.pop().unwrap();

        if terms.is_empty() {
            Self::assign(self, ctx, &ColumnID::A, &corner)?;
            self.empty_cell(ctx, &ColumnID::B)?;
            self.empty_cell(ctx, &ColumnID::C)?;

            self.set_constant(ctx, constant)?;
            self.disable_next(ctx)?;
            self.disable_mul(ctx)?;
            self.next(ctx)?;
            return Ok(());
        }

        // if not only one corner value is disallowed to be ranged
        // since it is likely a sum of rest or the terms
        assert!(corner.witness.range.is_none(),);

        const CHUNK_SIZE: usize = 2;

        let number_of_chunks = ((terms.len() as i32 - 1) / CHUNK_SIZE as i32) + 1;
        let number_of_chunks = number_of_chunks as usize;

        let mut sum = corner.value();

        for (i, chunk) in terms.chunks(CHUNK_SIZE).enumerate() {
            // shape the gate:
            // * first degree composition has no mul
            self.disable_mul(ctx)?;
            // * enable next if not last chunk
            if i == number_of_chunks - 1 {
                self.disable_next(ctx)?;
            } else {
                self.enable_scaled_next(ctx, -F::ONE)?;
            }

            // add constant with the first chunk
            let constant = if i == 0 { constant } else { F::ZERO };
            self.set_constant(ctx, constant)?;

            // terms
            Self::assign(self, ctx, &ColumnID::A, &chunk[0])?;

            if chunk.len() == CHUNK_SIZE {
                Self::assign(self, ctx, &ColumnID::B, &chunk[1])?;
            } else {
                self.empty_cell(ctx, &ColumnID::B)?;
            }

            // intermediate
            let t = if i == 0 {
                corner
            } else {
                Witness::tmp(sum).into()
            };
            Self::assign(self, ctx, &ColumnID::C, &t)?;

            // update running sum
            sum = sum + Scaled::compose(chunk, constant);

            self.next(ctx)?;
        }
        Ok(())
    }

    fn zero_sum_second_degree(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        terms: &[Term<F>],
        constant: F,
    ) -> Result<(), Error> {
        let mut first_degree_terms: Vec<Scaled<F>> = terms
            .iter()
            .filter_map(|term| match term {
                Term::First(term) => Some(*term),
                _ => None,
            })
            .collect();

        let second_degree_terms: Vec<SecondDegreeScaled<F>> = terms
            .iter()
            .filter_map(|term| match term {
                Term::Second(term) => Some(*term),
                _ => None,
            })
            .collect();

        assert_eq!(
            first_degree_terms.len() + second_degree_terms.len(),
            terms.len(),
            "no zero term"
        );

        if second_degree_terms.is_empty() {
            return self.zero_sum(ctx, &first_degree_terms, constant);
        }

        let corner = if let Some(term) = first_degree_terms.pop() {
            term
        } else {
            Scaled::tmp(
                second_degree_terms
                    .first()
                    .unwrap()
                    .value()
                    .map(|_| F::ZERO),
                F::ZERO,
            )
        };

        let mut sum = corner.value();

        for (i, term) in second_degree_terms.iter().enumerate() {
            // shape the gate:
            // * open mul gate
            self.enable_scaled_mul(ctx, term.factor)?;
            // * decide next gate
            if i == second_degree_terms.len() - 1 {
                if !first_degree_terms.is_empty() {
                    self.enable_scaled_next(ctx, -F::ONE)?;
                } else {
                    self.disable_next(ctx)?;
                }
            } else {
                self.enable_scaled_next(ctx, -F::ONE)?;
            }

            // add constant in first iter
            let constant = if i == 0 { constant } else { F::ZERO };
            self.set_constant(ctx, constant)?;

            // assign second degree term
            Self::assign(self, ctx, &ColumnID::A, &Scaled::mul(&term.w0))?;
            Self::assign(self, ctx, &ColumnID::B, &Scaled::mul(&term.w1))?;

            // intermediate
            let t = if i == 0 {
                corner
            } else {
                Witness::tmp(sum).into()
            };
            Self::assign(self, ctx, &ColumnID::C, &t)?;

            // update running sum
            sum = sum + term.value().map(|term| term + constant);

            // proceed to the next row
            self.next(ctx)?;
        }

        // constraint the rest of the first degree terms
        if !first_degree_terms.is_empty() {
            first_degree_terms.push(Witness::tmp(sum).into());
            self.zero_sum(ctx, &first_degree_terms, F::ZERO)?;
        }
        Ok(())
    }
}

// impl<F: PrimeField + Ord> GateLayout<F, &[CompositionEnforcement<F>]> for VanillaGate<F> {
//     fn layout<L: Layouter<F>>(
//         &self,
//         #[cfg(feature = "info")] annotation: String,
//         ly_ctx: &mut LayoutCtx<F, L>,
//         e: &[CompositionEnforcement<F>],
//     ) -> Result<(), Error> {
//         let _offset = ly_ctx.layouter.assign_region(
//
//             |region| {
//                 let ctx = &mut crate::RegionCtx::new(
//                     region,
//                     &mut ly_ctx.cell_map,
//                     &mut ly_ctx.bit_size_tags,
//                 );

//                 // for op in e.complex.iter() {
//                 //     ComplexAssignment::assign(self, ctx, op)?;
//                 // }

//                 for op in e.iter() {
//                     CompositionAssignment::assign(self, ctx, op)?;
//                 }

//                 self.empty_row(ctx)?;

//                 Ok(ctx.offset())
//             },
//         )?;

//         Ok(())
//     }
// }

// impl<F: PrimeField + Ord> GateLayout<F, &[SelectionEnforcement<F>]> for VanillaGate<F> {
//     fn layout<L: Layouter<F>>(
//         &self,
//         #[cfg(feature = "info")] annotation: String,
//         ly_ctx: &mut LayoutCtx<F, L>,
//         e: &[SelectionEnforcement<F>],
//     ) -> Result<(), Error> {
//         let _offset = ly_ctx.layouter.assign_region(
//
//             |region| {
//                 let ctx = &mut crate::RegionCtx::new(
//                     region,
//                     &mut ly_ctx.cell_map,
//                     &mut ly_ctx.bit_size_tags,
//                 );

//                 for op in e.iter() {
//                     ComplexAssignment::assign(self, ctx, op)?;
//                 }

//                 self.empty_row(ctx)?;

//                 Ok(ctx.offset())
//             },
//         )?;

//         Ok(())
//     }
// }

// impl<F: PrimeField + Ord> GateLayout<F, &[(u32, u32)]> for VanillaGate<F> {
//     fn layout<L: Layouter<F>>(
//         &self,
//         #[cfg(feature = "info")] annotation: String,
//         ly_ctx: &mut LayoutCtx<F, L>,
//         e: &[(u32, u32)],
//     ) -> Result<(), Error> {
//         ly_ctx.layouter.assign_region(
//
//             |region| {
//                 let ctx = &mut crate::RegionCtx::new(
//                     region,
//                     &mut ly_ctx.cell_map,
//                     &mut ly_ctx.bit_size_tags,
//                 );

//                 for (id0, id1) in e.iter() {
//                     ctx.copy(*id0, *id1)?;
//                 }

//                 Ok(())
//             },
//         )?;

//         Ok(())
//     }
// }

// #[cfg(test)]
// fn assert_equal(
//     &self,
//     ctx: &mut RegionCtx<'_, '_, F>,
//     w0: &Witness<F>,
//     other: &Witness<F>,
// ) -> Result<(), Error> {
//     self.disable_next(ctx)?;
//     self.disable_constant(ctx)?;
//     self.disable_mul(ctx)?;
//     AritmeticAssigment::assign(self, ctx, &ColumnID::A, &Scaled::add(w0))?;
//     AritmeticAssigment::assign(self, ctx, &ColumnID::B, &Scaled::sub(other))?;
//     self.empty_cell(ctx, &ColumnID::C).map(|_| ())
// }
