use super::{
    range::{RangeInPlace, RangeTableLayout},
    GateLayout,
};
use crate::{
    enforcement::{FirstDegreeComposition, Selection},
    gates::range::sort_by_size,
    witness::{Composable, Witness},
    LayoutCtx,
};
use ff::PrimeField;
use halo2_pse::{
    circuit::{Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Fixed, Selector},
    poly::Rotation,
};
use std::{collections::BTreeMap, marker::PhantomData};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Selectors {
    Eq,
    Acc,
    Select,
}

#[derive(Clone, Debug)]
pub struct VerticalGate<F: PrimeField, R: RangeInPlace<F, 1>> {
    pub(crate) constant: Column<Fixed>,
    pub(crate) range_gate: R,
    pub(crate) advice: Column<Advice>,
    pub(crate) acc: Column<Advice>,
    pub(crate) _marker: PhantomData<F>,
    selectors: BTreeMap<Selectors, Selector>,
}

impl<F: PrimeField, R: RangeInPlace<F, 1>> VerticalGate<F, R> {
    pub fn new(
        _meta: &mut ConstraintSystem<F>,
        range_gate: R,

        constant: Column<Fixed>,
        advice: Column<Advice>,
        acc: Column<Advice>,
    ) -> Self {
        VerticalGate {
            selectors: BTreeMap::new(),
            constant,
            advice,
            acc,
            range_gate,
            _marker: PhantomData,
        }
    }

    pub fn configure_composition_gate(&mut self, meta: &mut ConstraintSystem<F>) {
        meta.enable_equality(self.advice);
        let acc_selector = meta.selector();
        let eq_selector = meta.selector();

        // prevent double composition config

        assert!(self
            .selectors
            .insert(Selectors::Eq, eq_selector.clone())
            .is_none());

        assert!(self
            .selectors
            .insert(Selectors::Acc, acc_selector.clone())
            .is_none());

        meta.create_gate("vertical composition w/o equality", |meta| {
            let acc_selector = meta.query_selector(acc_selector);
            let eq_selector = meta.query_selector(eq_selector);

            let constant = meta.query_fixed(self.constant, Rotation::cur());
            let advice = meta.query_advice(self.advice, Rotation::cur());
            let acc_prev = meta.query_advice(self.acc, Rotation::prev());
            let acc = meta.query_advice(self.acc, Rotation::cur());

            // we may open this if we like to include constant addition kind of operations in the gate
            // let mul_advice = constant.clone() * advice.clone();
            // let add_advice = constant.clone() + advice.clone();
            // let term = eq_selector.clone() * add_advice
            //     + (Expression::Constant(F::ONE) - eq_selector.clone()) * mul_advice;

            let term = constant * advice;

            let expression_acc = acc_selector * (acc_prev.clone() + term - acc.clone());
            let expression_eq = eq_selector * acc;

            vec![expression_acc, expression_eq]
        });
    }

    pub fn configure_selection_gate(&mut self, meta: &mut ConstraintSystem<F>) {
        meta.enable_equality(self.advice);
        meta.enable_equality(self.acc);

        let selection_selector = meta.selector();

        assert!(self
            .selectors
            .insert(Selectors::Eq, selection_selector.clone())
            .is_some());

        meta.create_gate("selection", |meta| {
            let selector = meta.query_selector(selection_selector);

            let w0 = meta.query_advice(self.acc, Rotation::cur());
            let selected = meta.query_advice(self.advice, Rotation::cur());
            let w1 = meta.query_advice(self.acc, Rotation::next());
            let cond = meta.query_advice(self.advice, Rotation::next());

            // c*w0 - c*w1 + w1 - res = 0
            // c * (w0 - w1) + w1 - res = 0
            let expression =
                cond.clone() * (w0.clone() - w1.clone()) + w1.clone() - selected.clone();
            Constraints::with_selector(selector, vec![expression])
        });
    }
}

impl<F: PrimeField + Ord, R: RangeInPlace<F, 1>> GateLayout<F, Vec<Selection<F>>>
    for VerticalGate<F, R>
{
    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<Selection<F>>,
    ) -> Result<(), Error> {
        #[cfg(feature = "info")]
        {
            println!("---");
            println!("vertical gate, selects");
            println!("* number of selects: {}", e.len());
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut crate::RegionCtx::new(region, &mut ly_ctx.cell_map);
                for op in e.iter() {
                    ctx.enable(*self.selectors.get(&Selectors::Select).unwrap())?;

                    let cell = ctx.advice(self.acc.into(), op.w0.value())?;
                    ctx.copy_chain(op.w0.id.expect("should be copiable"), cell)?;
                    let cell = ctx.advice(self.advice.into(), op.selected.value())?;
                    ctx.copy_chain(op.selected.id.expect("should be copiable"), cell)?;

                    ctx.next();

                    let cell = ctx.advice(self.acc.into(), op.w1.value())?;
                    ctx.copy_chain(op.w1.id.expect("should be copiable"), cell)?;
                    let cell = ctx.advice(self.advice.into(), op.cond.value())?;
                    ctx.copy_chain(op.cond.id.expect("should be copiable"), cell)?;

                    ctx.next();
                }

                ctx.empty(self.acc.into())?; // can be any
                ctx.empty(self.advice.into())?; // must be zero
                ctx.empty(self.constant.into())?; // must be zero
                                                  // ctx.enable(self.eq_selector)?; // force that initial acc is zero
                ctx.next();
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

impl<F: PrimeField + Ord, R: RangeInPlace<F, 1>> GateLayout<F, Vec<FirstDegreeComposition<F>>>
    for VerticalGate<F, R>
{
    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<FirstDegreeComposition<F>>,
    ) -> Result<(), Error> {
        #[cfg(feature = "info")]
        {
            let mut n: BTreeMap<usize, usize> = BTreeMap::new();

            for op in e.iter() {
                n.entry(op.terms.len())
                    .and_modify(|count| *count += 1)
                    .or_insert_with(|| 1);
            }

            println!("---");
            println!("vertical gate, first degree compositions");
            println!("* number of compositions: {}", e.len());
            for (n_terms, count) in n {
                println!("* * zerosum n: {n_terms} occurs: {count}");
            }
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut crate::RegionCtx::new(region, &mut ly_ctx.cell_map);

                // FIX: escape from wrap back error
                ctx.empty(self.acc.into())?; // can be any
                ctx.empty(self.advice.into())?; // must be zero
                ctx.empty(self.constant.into())?; // must be zero
                                                  // ctx.enable(self.eq_selector)?; // force that initial acc is zero
                ctx.next();

                for composition in e.iter() {
                    let constant = composition.constant;
                    assert_eq!(constant, F::ZERO, "no constant addition in vertical gate");

                    let n = composition.terms.len();
                    let mut acc = Value::known(F::ZERO);

                    // a0 | a0
                    // a1 | a0 + a1
                    // a2 | a0 + a1 + a2
                    // .. |
                    // a  | 0

                    // so that accumulator of next composition starts from zero!
                    assert!(!composition.terms.is_empty());

                    // this is an edge case that we exploit using as simple assignment
                    if composition.terms.len() == 1 {
                        let term = composition.terms.first().unwrap();
                        assert_eq!(term.factor, F::ONE);
                        let witness = term.witness;
                        // assign limb
                        let cell = ctx.advice(self.advice, witness.value())?;
                        // apply copy
                        ctx.copy_chain(witness.id.expect("must be copiable"), cell)?;

                        ctx.empty(self.constant.into())?;
                        ctx.empty(self.acc.into())?;
                        ctx.enable(*self.selectors.get(&Selectors::Eq).unwrap())?;
                        ctx.next();
                        continue;
                    }

                    for (i, term) in composition.terms.iter().enumerate() {
                        let scale = term.factor;
                        let witness = term.witness;
                        let is_last = i == n - 1;
                        // if always open do we need it?
                        ctx.enable(*self.selectors.get(&Selectors::Acc).unwrap())?;

                        // assign limb
                        let cell = ctx.advice(self.advice, witness.value())?;
                        // apply copy
                        ctx.copy_chain(witness.id.expect("must be copiable"), cell)?;

                        // update accumulator
                        acc = acc.zip(term.value()).map(|(acc, term)| acc + term);
                        // assign accumulator
                        ctx.advice(self.acc, acc)?;

                        if is_last {
                            // expect zero at the last accumulator
                            ctx.enable(*self.selectors.get(&Selectors::Eq).unwrap())?;
                            assert_eq!(scale, -F::ONE, "don't scale the composition result");
                        } else {
                            // open range gate if needed
                            if let Some(range) = witness.range {
                                self.range_gate.enable(ctx, 0, range)?;
                            }
                        }

                        // scale
                        ctx.fixed(self.constant, scale)?;

                        #[cfg(feature = "synth-sanity")]
                        {
                            if is_last {
                                assert!(witness.range.is_none());
                            } else {
                                // assert!(witness.range.is_some());
                            }
                        }

                        #[cfg(feature = "prover-sanity")]
                        {
                            if is_last {
                                acc.map(|acc| {
                                    assert_eq!(acc, F::ZERO);
                                });
                            }
                        }

                        ctx.next();
                    }
                }

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

impl<F: PrimeField, R: RangeInPlace<F, 1>> RangeTableLayout<F> for VerticalGate<F, R> {
    fn layout_range_tables<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        bit_sizes: &[usize],
    ) -> Result<(), Error> {
        self.range_gate.layout_range_tables(ly_ctx, bit_sizes)
    }
}

impl<F: PrimeField + Ord, R: RangeInPlace<F, 1>> GateLayout<F, Vec<Witness<F>>>
    for VerticalGate<F, R>
{
    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<Witness<F>>,
    ) -> Result<(), Error> {
        #[cfg(feature = "info")]
        {
            let sorted = sort_by_size(&e[..], None);
            let n: usize = sorted.values().map(|e| e.len()).sum();
            println!("---");
            println!("* number of ranged witnesses: {}", n);
            for (bit_size, witnesses) in sorted.iter() {
                println!("* * bit_size: {} occurs: {}", bit_size, witnesses.len());
            }
            println!()
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut crate::RegionCtx::new(region, &mut ly_ctx.cell_map);
                self.range_gate.assign_remainings(ctx, &e, [self.advice])?;
                Ok(ctx.offset())
            },
        )?;

        Ok(())
    }
}
