use super::GateLayout;
use crate::circuitry::{
    enforcement::{FirstDegree, SecondDegree, Selection},
    witness::{Composable, Scaled, SecondDegreeScaled, Term, Witness},
    LayoutCtx, RegionCtx,
};
use ff::PrimeField;
use halo2::{
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

#[derive(Clone, Debug)]
pub struct VarVanillaGate<F: PrimeField, const W: usize> {
    pub(crate) selector: Selector,
    pub(crate) s_mul: Column<Fixed>,
    pub(crate) advice: [Column<Advice>; W],
    pub(crate) fixed: [Column<Fixed>; W],
    pub(crate) s_next: Column<Fixed>,
    pub(crate) constant: Column<Fixed>,

    // pub(crate) _public_inputs: Option<Column<Instance>>,
    pub(crate) _marker: PhantomData<F>,
}

impl<F: PrimeField, const W: usize> VarVanillaGate<F, W> {
    pub fn advice_colums(&self) -> [Column<Advice>; W] {
        self.advice
    }

    pub fn fixed_columns(&self) -> [Column<Fixed>; W] {
        self.fixed
    }

    pub fn constant(&self) -> Column<Fixed> {
        self.constant
    }

    fn column(&self, idx: usize) -> (Column<Fixed>, Column<Advice>) {
        (self.fixed[idx], self.advice[idx])
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
        ctx.fixed(self.s_next, factor).map(|_| ())
    }

    fn disable_next(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        ctx.fixed(self.s_next, F::ZERO).map(|_| ())
    }

    fn set_constant(&self, ctx: &mut RegionCtx<'_, '_, F>, constant: F) -> Result<(), Error> {
        ctx.fixed(self.constant, constant).map(|_| ())
    }

    fn assign(
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
        let _ = self
            .fixed
            .iter()
            .map(|column| ctx.fixed(*column, F::ZERO))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(())
    }

    fn empty_row(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        self.no_op(ctx)?;
        self.no_witness(ctx)?;
        ctx.next();
        Ok(())
    }

    fn empty_cell(&self, ctx: &mut RegionCtx<'_, '_, F>, column: usize) -> Result<(), Error> {
        let (fixed, advice) = self.column(column);
        ctx.fixed(fixed, F::ZERO)?;
        ctx.advice(advice, Value::known(F::ZERO))?;
        Ok(())
    }

    fn no_witness(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        for i in 0..W {
            self.empty_cell(ctx, i)?;
        }
        Ok(())
    }
}

impl<F: PrimeField + Ord, const W: usize> VarVanillaGate<F, W> {
    pub fn new(meta: &mut ConstraintSystem<F>) -> Self {
        let selector = meta.selector();

        let advice = (0..W)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let fixed = (0..W)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let s_mul = meta.fixed_column();
        let (s_next, constant) = (meta.fixed_column(), meta.fixed_column());
        // let public_inputs = meta.instance_column();

        Self {
            selector,
            advice,
            fixed,
            s_mul,
            s_next,
            constant,
            _marker: PhantomData,
        }
    }

    pub fn configure(&self, meta: &mut ConstraintSystem<F>) {
        let _ = self
            .advice
            .iter()
            .map(|column| meta.enable_equality(*column))
            .collect::<Vec<_>>();

        meta.create_gate("vanilla gate", |meta| {
            let advices = self
                .advice
                .iter()
                .map(|column| meta.query_advice(*column, Rotation::cur()))
                .collect::<Vec<_>>();
            let fixed = self
                .fixed
                .iter()
                .map(|column| meta.query_fixed(*column, Rotation::cur()))
                .collect::<Vec<_>>();

            let s_mul = meta.query_fixed(self.s_mul, Rotation::cur());

            let mul_expression = s_mul * advices[0].clone() * advices[1].clone();
            let add_xpression = advices.iter().skip(1).zip(fixed.iter().skip(1)).fold(
                advices[0].clone() * fixed[0].clone(),
                |acc, (advice, fixed)| acc + advice.clone() * fixed.clone(),
            );

            let s_next = meta.query_fixed(self.s_next, Rotation::cur());
            let next_advice = meta.query_advice(*self.advice.last().unwrap(), Rotation::next());
            let next_expression = s_next * next_advice;

            let constant_expression = meta.query_fixed(self.constant, Rotation::cur());

            let expression = mul_expression + add_xpression + next_expression + constant_expression;

            Constraints::with_selector(meta.query_selector(self.selector), vec![expression])
        });
    }
}

impl<F: PrimeField + Ord, const W: usize> GateLayout<F, Vec<FirstDegree<F>>>
    for VarVanillaGate<F, W>
{
    type Output = ();

    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<FirstDegree<F>>,
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
            println!("var vanilla gate, first degree composition");
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

impl<F: PrimeField + Ord, const W: usize> GateLayout<F, Vec<SecondDegree<F>>>
    for VarVanillaGate<F, W>
{
    type Output = ();

    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<SecondDegree<F>>,
    ) -> Result<(), Error> {
        #[cfg(feature = "info")]
        {
            let mut n_second: BTreeMap<(usize, usize), usize> = BTreeMap::new();
            println!("---");
            println!("var vanilla gate, second degree composition");
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
                println!(
                    "* zerosum n: {} nn: {} occurs: {}",
                    n_terms.0, n_terms.1, count
                );
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

impl<F: PrimeField + Ord, const W: usize> GateLayout<F, Vec<Selection<F>>>
    for VarVanillaGate<F, W>
{
    type Output = ();

    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<Selection<F>>,
    ) -> Result<(), Error> {
        #[cfg(feature = "info")]
        {
            println!("---");
            println!("var vanilla gate, selection");
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

impl<F: PrimeField, const W: usize> VarVanillaGate<F, W> {
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
        self.assign(ctx, 0, &Scaled::add(w1))?;
        self.assign(ctx, 1, &Scaled::mul(cond))?;
        for idx in 2..W - 1 {
            self.empty_cell(ctx, idx)?;
        }
        self.assign(ctx, W - 1, &Scaled::sub(selected))?;
        self.next(ctx)?;
        // * second row
        // c * w0 = -tmp
        // find the temp witenss
        let c_w0 = cond.value() * w0.value();
        let c_w0 = Scaled::tmp(c_w0, -F::ONE);
        self.enable_mul(ctx)?;
        self.disable_next(ctx)?;
        self.disable_constant(ctx)?;
        self.assign(ctx, 0, &Scaled::mul(w0))?;
        self.assign(ctx, 1, &Scaled::mul(cond))?;
        for idx in 2..W - 1 {
            self.empty_cell(ctx, idx)?;
        }
        self.assign(ctx, W - 1, &c_w0)?;
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
    //     self.assign(ctx, 0, &Scaled::sub(w0))?;
    //     self.assign(ctx, 1, &Scaled::sub(w1))?;
    //     for idx in 2..W - 1 {
    //         self.empty_cell(ctx, idx)?;
    //     }
    //     self.assign(ctx, W - 1, &Scaled::add(result))?;
    //     self.next(ctx)?;
    //     Ok(())
    // }

    fn zero_sum(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        terms: &[Scaled<F>],
        constant: F,
    ) -> Result<(), Error> {
        let mut terms = terms.to_vec();
        let corner = terms.pop().unwrap();

        if terms.is_empty() {
            self.assign(ctx, 0, &corner)?;

            for idx in 1..W {
                self.empty_cell(ctx, idx)?;
            }

            self.set_constant(ctx, constant)?;
            self.disable_next(ctx)?;
            self.disable_mul(ctx)?;
            self.next(ctx)?;
            return Ok(());
        }

        let chunk_size: usize = W - 1;

        let number_of_chunks = ((terms.len() as i32 - 1) / chunk_size as i32) + 1;
        let number_of_chunks = number_of_chunks as usize;

        let mut sum = corner.value();

        for (i, chunk) in terms.chunks(chunk_size).enumerate() {
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

            for (j, e) in chunk.iter().enumerate() {
                self.assign(ctx, j, e)?;
            }
            for j in chunk.len()..chunk_size {
                self.empty_cell(ctx, j)?;
            }

            // intermediate
            let t = if i == 0 {
                corner
            } else {
                Witness::tmp(sum).into()
            };
            self.assign(ctx, chunk_size, &t)?;

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
            // TODO: consider disallowing such case
            return self.zero_sum(ctx, &first_degree_terms, constant);
        }

        // use the first corner as the running sum
        // and save one space of single term
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

        // split simultaneus first degree term
        let w_first_degree = W - 3;
        let (first_degree_terms, first_degree_terms_rest) = if w_first_degree > 0 {
            let offset = std::cmp::min(
                w_first_degree * second_degree_terms.len(),
                first_degree_terms.len(),
            );
            first_degree_terms.split_at(offset)
        } else {
            (&[] as &[Scaled<_>], &first_degree_terms[..])
        };

        // prepare first degree terms for the zipped iteration
        let first_degree_terms = if w_first_degree == 0 {
            std::iter::repeat(vec![])
                .take(second_degree_terms.len())
                .collect::<Vec<_>>()
        } else {
            first_degree_terms
                .chunks(w_first_degree)
                .map(|chunk| {
                    // Some(
                    chunk
                        .iter()
                        .map(Some)
                        .chain(std::iter::repeat(None))
                        .take(w_first_degree)
                        .collect::<Vec<_>>()
                    // )
                })
                .chain(std::iter::repeat(vec![None; w_first_degree]))
                .take(second_degree_terms.len())
                .collect::<Vec<_>>()
        };

        for (i, (second_degree_term, first_degree_terms)) in second_degree_terms
            .iter()
            .zip(first_degree_terms.iter())
            .enumerate()
        {
            let in_last_iter = i == second_degree_terms.len() - 1;

            // shape the gate:
            // * open mul gate
            self.enable_scaled_mul(ctx, second_degree_term.factor)?;
            // * decide next gate
            if in_last_iter {
                if !first_degree_terms_rest.is_empty() {
                    // if there is first degree terms left running sum will continue
                    self.enable_scaled_next(ctx, -F::ONE)?;
                } else {
                    // it should mean we are exhausted of terms
                    self.disable_next(ctx)?;
                }
            } else {
                // not the last term then continue adding up
                self.enable_scaled_next(ctx, -F::ONE)?;
            }

            // feed constant in the first iter
            let constant = if i == 0 { constant } else { F::ZERO };
            self.set_constant(ctx, constant)?;

            // assign second degree term
            self.assign(ctx, 0, &Scaled::mul(&second_degree_term.w0))?;
            self.assign(ctx, 1, &Scaled::mul(&second_degree_term.w1))?;

            // assign running sum before update
            let t = if i == 0 {
                corner
            } else {
                Witness::tmp(sum).into()
            };
            self.assign(ctx, W - 1, &t)?;

            // update running sum
            sum = sum + second_degree_term.value().map(|term| term + constant);

            assert_eq!(first_degree_terms.len(), W - 3);
            for (idx, first_degree_term) in first_degree_terms.iter().enumerate() {
                let idx = idx + 2;
                match first_degree_term {
                    Some(term) => {
                        self.assign(ctx, idx, term)?;
                        // update running sum
                        sum = sum + term.value();
                    }
                    // partially filled
                    None => {
                        self.empty_cell(ctx, idx)?;
                    }
                }
            }

            #[cfg(feature = "prover-sanity")]
            if in_last_iter && first_degree_terms_rest.is_empty() {
                sum.map(|sum| assert_eq!(sum, F::ZERO));
            }

            // proceed to the next row
            self.next(ctx)?;
        }

        let mut first_degree_terms_rest = first_degree_terms_rest.to_vec();
        if !first_degree_terms_rest.is_empty() {
            first_degree_terms_rest.push(Witness::tmp(sum).into());
            self.zero_sum(ctx, &first_degree_terms_rest, F::ZERO)?;
        }

        Ok(())
    }
}
