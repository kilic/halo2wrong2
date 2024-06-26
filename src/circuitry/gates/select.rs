use ff::PrimeField;
use halo2::{
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Selector},
    poly::Rotation,
};

use crate::circuitry::{enforcement::Selection, witness::Composable, LayoutCtx};

use super::GateLayout;

#[derive(Clone, Debug)]
pub struct SelectGate {
    pub(crate) selector: Selector,

    pub(crate) cond: Column<Advice>,
    pub(crate) w0: Column<Advice>,
    pub(crate) w1: Column<Advice>,
    pub(crate) selected: Column<Advice>,
}

impl SelectGate {
    #[allow(clippy::too_many_arguments)]
    pub fn configure<F: PrimeField>(
        meta: &mut ConstraintSystem<F>,
        cond: Column<Advice>,
        w0: Column<Advice>,
        w1: Column<Advice>,
        selected: Column<Advice>,
    ) -> Self {
        meta.enable_equality(cond);
        meta.enable_equality(w0);
        meta.enable_equality(w1);
        meta.enable_equality(selected);

        let selector = meta.selector();

        meta.create_gate("select", |meta| {
            let cond = meta.query_advice(cond, Rotation::cur());
            let w0 = meta.query_advice(w0, Rotation::cur());
            let w1 = meta.query_advice(w1, Rotation::cur());
            let selected = meta.query_advice(selected, Rotation::cur());
            let selector = meta.query_selector(selector);
            let expression = cond * (w0 - w1.clone()) + w1 - selected;
            Constraints::with_selector(selector, vec![expression])
        });

        Self {
            selector,
            cond,
            w0,
            w1,
            selected,
        }
    }
}

impl<F: PrimeField + Ord> GateLayout<F, Vec<Selection<F>>> for SelectGate {
    type Output = ();

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
                let ctx = &mut crate::circuitry::RegionCtx::new(region, &mut ly_ctx.cell_map);
                for op in e.iter() {
                    ctx.enable(self.selector)?;
                    let cond = op.cond;
                    let w0 = op.w0;
                    let w1 = op.w1;
                    let selected = op.selected;

                    let cell = ctx.advice(self.cond, cond.value())?;
                    ctx.copy_chain(cond.id().expect("must be registered witness"), cell)?;
                    let cell = ctx.advice(self.w0, w0.value())?;
                    ctx.copy_chain(w0.id().expect("must be registered witness"), cell)?;
                    let cell = ctx.advice(self.w1, w1.value())?;
                    ctx.copy_chain(w1.id().expect("must be registered witness"), cell)?;
                    let cell = ctx.advice(self.selected, selected.value())?;
                    ctx.copy_chain(selected.id().expect("must be registered witness"), cell)?;

                    ctx.next();
                }

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
