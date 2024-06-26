use super::GateLayout;
use crate::circuitry::{
    witness::{Composable, Scaled, SecondDegreeScaled, Term, Witness},
    LayoutCtx, RegionCtx,
};
use ff::PrimeField;
use halo2::{
    circuit::{Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Fixed, Selector},
    poly::Rotation,
};
use std::collections::BTreeMap;

#[derive(Clone, Debug)]
pub struct VanillaGate {
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
}

impl VanillaGate {
    pub fn advice_colums(&self) -> [Column<Advice>; 3] {
        [self.a, self.b, self.c]
    }

    pub fn fixed_columns(&self) -> [Column<Fixed>; 3] {
        [self.sa, self.sb, self.sc]
    }

    pub fn constant(&self) -> Column<Fixed> {
        self.constant.unwrap()
    }

    fn column(&self, idx: usize) -> (Column<Fixed>, Column<Advice>) {
        match idx {
            0 => (self.sa, self.a),
            1 => (self.sb, self.b),
            2 => (self.sc, self.c),
            _ => panic!("invalid column index"),
        }
    }

    fn enable<F: PrimeField>(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        ctx.enable(self.selector)
    }

    fn next<F: PrimeField>(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        self.enable(ctx)?;
        ctx.next();
        Ok(())
    }

    fn enable_scaled_mul<F: PrimeField>(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        factor: F,
    ) -> Result<(), Error> {
        ctx.fixed(self.s_mul, factor).map(|_| ())
    }

    fn enable_scaled_next<F: PrimeField>(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        factor: F,
    ) -> Result<(), Error> {
        if let Some(column) = self.s_next {
            ctx.fixed(column, factor).map(|_| ())
        } else {
            Ok(())
        }
    }

    fn disable_next<F: PrimeField>(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        if let Some(column) = self.s_next {
            ctx.fixed(column, F::ZERO).map(|_| ())
        } else {
            Ok(())
        }
    }

    fn set_constant<F: PrimeField>(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        constant: F,
    ) -> Result<(), Error> {
        if let Some(column) = self.constant {
            ctx.fixed(column, constant).map(|_| ())
        } else {
            Ok(())
        }
    }

    fn assign<F: PrimeField>(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        idx: usize,
        e: &Scaled<F>,
    ) -> Result<(), Error> {
        // resolve column
        let (fixed, advice) = self.column(idx);
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

    fn disable_mul<F: PrimeField>(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        self.enable_scaled_mul(ctx, F::ZERO)
    }

    fn disable_constant<F: PrimeField>(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        self.set_constant(ctx, F::ZERO)
    }

    fn enable_mul<F: PrimeField>(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        self.enable_scaled_mul(ctx, F::ONE)
    }

    fn enable_next<F: PrimeField>(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        self.enable_scaled_next(ctx, F::ONE)
    }

    fn no_op<F: PrimeField>(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        self.disable_constant(ctx)?;
        self.disable_mul(ctx)?;
        self.disable_next(ctx)?;
        ctx.empty(self.sa.into())?;
        ctx.empty(self.sb.into())?;
        ctx.empty(self.sc.into())?;
        Ok(())
    }

    fn empty_row<F: PrimeField>(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        self.no_op(ctx)?;
        self.no_witness(ctx)?;
        ctx.next();
        Ok(())
    }

    fn empty_cell<F: PrimeField>(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        idx: usize,
    ) -> Result<(), Error> {
        let (fixed, advice) = self.column(idx);
        ctx.fixed(fixed, F::ZERO)?;
        ctx.advice(advice, Value::known(F::ZERO))?;
        Ok(())
    }

    fn no_witness<F: PrimeField>(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        for c in 0..3 {
            self.empty_cell(ctx, c)?;
        }
        Ok(())
    }
}

impl VanillaGate {
    pub fn configure<F: PrimeField>(meta: &mut ConstraintSystem<F>) -> Self {
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

        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(c);
        meta.create_gate("vanilla gate", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let next = meta.query_advice(c, Rotation::next());
            let c = meta.query_advice(c, Rotation::cur());
            let sa = meta.query_fixed(sa, Rotation::cur());
            let sb = meta.query_fixed(sb, Rotation::cur());
            let sc = meta.query_fixed(sc, Rotation::cur());
            let s_mul = meta.query_fixed(s_mul, Rotation::cur());

            let mut expression = a.clone() * sa + b.clone() * sb + c * sc + a * b * s_mul;
            expression = expression + meta.query_fixed(constant, Rotation::cur());
            let s_next = meta.query_fixed(s_next, Rotation::cur());
            expression = expression + s_next * next;

            let selector = meta.query_selector(selector);
            Constraints::with_selector(selector, vec![expression])
        });

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
        }
    }
}

impl<F: PrimeField + Ord> GateLayout<F, Vec<crate::circuitry::enforcement::FirstDegree<F>>>
    for VanillaGate
{
    type Output = ();

    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<crate::circuitry::enforcement::FirstDegree<F>>,
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
                println!("* n: {n_terms} occurs: {count}");
            }
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut crate::circuitry::RegionCtx::new(region, &mut ly_ctx.cell_map);

                for op in e.iter() {
                    self.zero_sum(ctx, &op.terms, op.constant)?;
                }

                self.empty_row(ctx)?;

                Ok(ctx.offset())
            },
        )?;

        #[cfg(feature = "info")]
        {
            println!("* rows: {_offset}");
            println!();
        }

        Ok(())
    }
}

impl<F: PrimeField + Ord> GateLayout<F, Vec<crate::circuitry::enforcement::SecondDegree<F>>>
    for VanillaGate
{
    type Output = ();

    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<crate::circuitry::enforcement::SecondDegree<F>>,
    ) -> Result<(), Error> {
        #[cfg(feature = "info")]
        {
            let mut n_second: BTreeMap<(usize, usize), usize> = BTreeMap::new();
            println!("---");
            println!("* number of compositions: {}", e.len());

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
                println!("* n: {} nn: {} occurs: {}", n_terms.0, n_terms.1, count);
            }
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut crate::circuitry::RegionCtx::new(region, &mut ly_ctx.cell_map);

                for op in e.iter() {
                    self.zero_sum_second_degree(ctx, &op.terms, op.constant)?;
                }

                self.empty_row(ctx)?;

                Ok(ctx.offset())
            },
        )?;

        #[cfg(feature = "info")]
        {
            println!("* rows: {_offset}");
            println!();
        }

        Ok(())
    }
}

impl<F: PrimeField + Ord> GateLayout<F, Vec<crate::circuitry::enforcement::Selection<F>>>
    for VanillaGate
{
    type Output = ();

    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<crate::circuitry::enforcement::Selection<F>>,
    ) -> Result<(), Error> {
        #[cfg(feature = "info")]
        {
            println!("---");
            println!("* number of selects: {}", e.len());
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut crate::circuitry::RegionCtx::new(region, &mut ly_ctx.cell_map);
                for op in e.iter() {
                    self.select(ctx, &op.cond, &op.w0, &op.w1, &op.selected)?;
                }
                self.empty_row(ctx)?;
                Ok(ctx.offset())
            },
        )?;

        #[cfg(feature = "info")]
        {
            println!("* rows: {_offset}");
            println!();
        }

        Ok(())
    }
}

impl VanillaGate {
    fn select<F: PrimeField>(
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
        Self::assign(self, ctx, 0, &Scaled::add(w1))?;
        Self::assign(self, ctx, 1, &Scaled::mul(cond))?;
        Self::assign(self, ctx, 2, &Scaled::sub(selected))?;
        self.next(ctx)?;
        // * second row
        // c * w0 = -tmp
        // find the temp witenss
        let c_w0 = cond.value() * w0.value();
        let c_w0 = Scaled::tmp(c_w0, -F::ONE);
        self.enable_mul(ctx)?;
        self.disable_next(ctx)?;
        self.disable_constant(ctx)?;
        Self::assign(self, ctx, 0, &Scaled::mul(w0))?;
        Self::assign(self, ctx, 1, &Scaled::mul(cond))?;
        Self::assign(self, ctx, 2, &c_w0)?;
        self.next(ctx)
    }

    // fn or(
    //     &self,
    //     ctx: &mut RegionCtx<'_, '_, F>,
    //     w0: &Witness<F>,
    //     w1: &Witness<F>,
    //     result: &Witness<F>,
    // ) -> Result<(), Error> {
    //     self.disable_next(ctx)?;
    //     self.disable_constant(ctx)?;
    //     self.enable_mul(ctx)?;
    //     Self::assign(self, ctx, 0, &Scaled::sub(w0))?;
    //     Self::assign(self, ctx, 1, &Scaled::sub(w1))?;
    //     Self::assign(self, ctx, 2, &Scaled::add(result))?;
    //     self.next(ctx)?;
    //     Ok(())
    // }

    fn zero_sum<F: PrimeField>(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        terms: &[Scaled<F>],
        constant: F,
    ) -> Result<(), Error> {
        let mut terms = terms.to_vec();
        let corner = terms.pop().unwrap();

        if terms.is_empty() {
            Self::assign(self, ctx, 0, &corner)?;
            self.empty_cell(ctx, 1)?;
            self.empty_cell(ctx, 2)?;

            self.set_constant(ctx, constant)?;
            self.disable_next(ctx)?;
            self.disable_mul(ctx)?;
            self.next(ctx)?;
            return Ok(());
        }

        const CHUNK_SIZE: usize = 2;

        let number_of_chunks = ((terms.len() as i32 - 1) / CHUNK_SIZE as i32) + 1;
        let number_of_chunks = number_of_chunks as usize;

        let mut sum = corner.value();

        for (i, chunk) in terms.chunks(CHUNK_SIZE).enumerate() {
            let in_last_iter = i == number_of_chunks - 1;

            // shape the gate:
            // * first degree composition has no mul
            self.disable_mul(ctx)?;
            // * enable next if not last chunk
            if in_last_iter {
                self.disable_next(ctx)?;
            } else {
                self.enable_scaled_next(ctx, -F::ONE)?;
            }

            // add constant with the first chunk
            let constant = if i == 0 { constant } else { F::ZERO };
            self.set_constant(ctx, constant)?;

            // terms
            Self::assign(self, ctx, 0, &chunk[0])?;

            if chunk.len() == CHUNK_SIZE {
                Self::assign(self, ctx, 1, &chunk[1])?;
            } else {
                self.empty_cell(ctx, 1)?;
            }

            // intermediate
            let t = if i == 0 {
                corner
            } else {
                Witness::tmp(sum).into()
            };
            Self::assign(self, ctx, 2, &t)?;

            // update running sum
            sum = sum + Scaled::sum(chunk, constant);
            #[cfg(feature = "prover-sanity")]
            if in_last_iter {
                sum.map(|sum| assert_eq!(sum, F::ZERO));
            }

            self.next(ctx)?;
        }
        Ok(())
    }

    fn zero_sum_second_degree<F: PrimeField>(
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
            let in_last_iter = i == second_degree_terms.len() - 1;

            // shape the gate:
            // * open mul gate
            self.enable_scaled_mul(ctx, term.factor)?;
            // * decide next gate
            if in_last_iter {
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
            Self::assign(self, ctx, 0, &Scaled::mul(&term.w0))?;
            Self::assign(self, ctx, 1, &Scaled::mul(&term.w1))?;

            // intermediate
            let t = if i == 0 {
                corner
            } else {
                Witness::tmp(sum).into()
            };
            Self::assign(self, ctx, 2, &t)?;

            // update running sum
            sum = sum + term.value().map(|term| term + constant);
            #[cfg(feature = "prover-sanity")]
            if in_last_iter && first_degree_terms.is_empty() {
                sum.map(|sum| assert_eq!(sum, F::ZERO));
            }

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
