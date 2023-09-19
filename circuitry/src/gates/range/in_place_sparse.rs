use std::marker::PhantomData;

use crate::{witness::Witness, LayoutCtx, RegionCtx};
use ff::PrimeField;
use halo2::{
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, TableColumn},
    poly::Rotation,
};

use super::{layout_range_table, RangeInPlace, RangeTableLayout};

#[derive(Debug, Clone)]
pub struct RangeInPlaceSpaseGate<F: PrimeField, const W: usize, const BIT_SIZE: usize> {
    pub(crate) value_table: TableColumn,
    pub(crate) scale: Column<Fixed>,
    _marker: PhantomData<F>,
}

impl<F: PrimeField, const W: usize, const BIT_SIZE: usize> RangeTableLayout<F>
    for RangeInPlaceSpaseGate<F, W, BIT_SIZE>
{
    fn layout_range_tables<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        _bit_sizes: &[usize],
    ) -> Result<(), Error> {
        #[cfg(feature = "info")]
        {
            println!("---");
            println!("* in place sparse range table: {:?}", BIT_SIZE);
            println!();
        }
        layout_range_table(ly_ctx, self.value_table, BIT_SIZE)
    }
}

impl<F: PrimeField, const W: usize, const BIT_SIZE: usize> RangeInPlace<F, W>
    for RangeInPlaceSpaseGate<F, W, BIT_SIZE>
{
    fn enable(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        _idx: usize,
        _bit_size: usize,
    ) -> Result<(), Error> {
        ctx.fixed(self.scale, F::one())?;
        Ok(())
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        values: [Column<Advice>; W],
    ) -> RangeInPlaceSpaseGate<F, W, BIT_SIZE> {
        let scale = meta.fixed_column();
        let value_table = meta.lookup_table_column();

        for value in values.iter() {
            meta.lookup("lookup", |meta| {
                let value = meta.query_advice(*value, Rotation::cur());
                let scale = meta.query_fixed(scale, Rotation::cur());
                vec![(scale * value, value_table)]
            });
        }

        RangeInPlaceSpaseGate {
            scale,
            value_table,
            _marker: PhantomData,
        }
    }

    fn assign_remainings(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        ranges: &[Witness<F>],
        values: [Column<Advice>; W],
    ) -> Result<(), Error> {
        let assign = |ctx: &mut RegionCtx<'_, '_, F>, column: usize, witness: &Witness<F>| {
            let value = values[column];
            let new_cell = ctx.advice(value, witness.value)?;
            ctx.copy_chain(witness.id.expect("range values with copy id"), new_cell)
        };

        let remainings = super::sort_by_size(ranges, Some(BIT_SIZE));
        for (rem_size, witnesses) in remainings.iter() {
            let u = BIT_SIZE.checked_sub(*rem_size).unwrap();
            assert!(u > 0);
            let factor = (F::one() + F::one()).pow_vartime(&[u as u64]);

            for witnesses in witnesses.chunks(W) {
                ctx.fixed(self.scale, factor)?;

                for (i, witness) in witnesses.iter().enumerate() {
                    assign(ctx, i, witness)?;
                }
                ctx.next();
            }
        }

        Ok(())
    }
}
