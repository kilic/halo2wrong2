use crate::{witness::Witness, LayoutCtx, RegionCtx};
use ff::PrimeField;
use halo2_pse::{
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector, TableColumn},
    poly::Rotation,
};
use std::marker::PhantomData;

use super::{layout_tagged_range_tables, RangeInPlace, RangeTableLayout};

#[derive(Debug, Clone)]
pub struct NoRangeInPlaceGate {}

impl<F: PrimeField> RangeTableLayout<F> for NoRangeInPlaceGate {
    fn layout_range_tables<L: Layouter<F>>(
        &self,
        _ly_ctx: &mut LayoutCtx<F, L>,
        _bit_sizes: &[usize],
    ) -> Result<(), Error> {
        Ok(())
    }
}

impl<F: PrimeField, const W: usize> RangeInPlace<F, W> for NoRangeInPlaceGate {
    fn configure(_meta: &mut ConstraintSystem<F>, _values: [Column<Advice>; W]) -> Self {
        Self {}
    }

    fn enable(
        &self,
        _ctx: &mut RegionCtx<'_, '_, F>,
        _idx: usize,
        _bit_size: usize,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn assign_remainings(
        &self,
        _ctx: &mut RegionCtx<'_, '_, F>,
        _ranges: &[Witness<F>],
        _values: [Column<Advice>; W],
    ) -> Result<(), Error> {
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct RangeInPlaceGate<F: PrimeField, const W: usize> {
    pub(crate) selectors: [Selector; W],
    pub(crate) tags: [Column<Fixed>; W],
    pub(crate) value_table: TableColumn,
    pub(crate) tag_table: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: PrimeField, const W: usize> RangeTableLayout<F> for RangeInPlaceGate<F, W> {
    fn layout_range_tables<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        bit_sizes: &[usize],
    ) -> Result<(), Error> {
        #[cfg(feature = "info")]
        {
            println!("---");
            println!("* in place range table: {:?}", bit_sizes);
            println!();
        }
        layout_tagged_range_tables(ly_ctx, self.tag_table, self.value_table, bit_sizes)
    }
}

impl<F: PrimeField, const W: usize> RangeInPlace<F, W> for RangeInPlaceGate<F, W> {
    fn configure(
        meta: &mut ConstraintSystem<F>,
        values: [Column<Advice>; W],
    ) -> RangeInPlaceGate<F, W> {
        let tags: [_; W] = (0..W)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let selectors: [_; W] = (0..W)
            .map(|_| meta.complex_selector())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let tag_table = meta.lookup_table_column();
        let value_table = meta.lookup_table_column();

        for ((value, tag), selector) in values.iter().zip(tags.iter()).zip(selectors.iter()) {
            meta.lookup("lookup", |meta| {
                let selector = meta.query_selector(*selector);
                let value = meta.query_advice(*value, Rotation::cur());
                let tag = meta.query_fixed(*tag, Rotation::cur());
                vec![(tag, tag_table), (selector * value, value_table)]
            });
        }

        RangeInPlaceGate {
            selectors,
            tag_table,
            value_table,
            tags,
            _marker: PhantomData,
        }
    }

    fn enable(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        idx: usize,
        bit_size: usize,
    ) -> Result<(), Error> {
        ctx.enable(self.selectors[idx]).unwrap();
        let tag = F::from(bit_size as u64 + 1);
        ctx.fixed(self.tags[idx], tag)?;
        Ok(())
    }

    fn assign_remainings(
        &self,
        _ctx: &mut RegionCtx<'_, '_, F>,
        _ranges: &[Witness<F>],
        _values: [Column<Advice>; W],
    ) -> Result<(), Error> {
        Ok(())
    }
}
