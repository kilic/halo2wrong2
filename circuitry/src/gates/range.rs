use crate::{LayoutCtx, RegionCtx};
use ff::PrimeField;
use halo2::{
    circuit::{Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector, TableColumn},
};

use halo2::poly::Rotation;

#[derive(Debug, Clone)]
pub struct RangeGate {
    pub(crate) selector: Selector,
    pub(crate) tag: Column<Fixed>,
    pub(crate) value_table: TableColumn,
    pub(crate) tag_table: TableColumn,
}

impl RangeGate {
    pub fn configure<F: PrimeField>(
        meta: &mut ConstraintSystem<F>,
        advices: &[Column<Advice>],
    ) -> RangeGate {
        let tag = meta.fixed_column();
        let selector = meta.complex_selector();
        let tag_table = meta.lookup_table_column();
        let value_table = meta.lookup_table_column();

        for advice in advices.iter() {
            meta.lookup("lookup", |meta| {
                let selector = meta.query_selector(selector);
                let advice = meta.query_advice(*advice, Rotation::cur());
                let tag = meta.query_fixed(tag, Rotation::cur());
                vec![(tag, tag_table), (selector * advice, value_table)]
            });
        }

        RangeGate {
            selector,
            tag_table,
            value_table,
            tag,
        }
    }

    pub fn enable<F: PrimeField>(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        bit_size: usize,
    ) -> Result<(), Error> {
        ctx.enable(self.selector).unwrap();
        let tag = F::from(bit_size as u64 + 1);
        ctx.fixed(self.tag, tag)?;
        Ok(())
    }

    pub fn layout_range_tables<F: PrimeField, L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        bit_sizes: &[usize],
    ) -> Result<(), Error> {
        #[cfg(feature = "info")]
        {
            println!("---");
            println!("* range table: {bit_sizes:?}");
            println!();
        }
        layout_range_tables(ly_ctx, self.tag_table, self.value_table, bit_sizes)
    }
}

pub(crate) fn layout_range_tables<F: PrimeField, L: Layouter<F>>(
    ly_ctx: &mut LayoutCtx<F, L>,
    tag_table: TableColumn,
    value_table: TableColumn,
    bit_sizes: &[usize],
) -> Result<(), Error> {
    let mut bit_sizes = bit_sizes.to_vec();
    bit_sizes.sort();
    assert!(!bit_sizes.is_empty());
    assert_ne!(bit_sizes[0], 0);
    ly_ctx.layouter.assign_table(
        || "",
        |mut table| {
            let mut offset = 0;

            table.assign_cell(|| "table tag", tag_table, 0, || Value::known(F::ZERO))?;
            table.assign_cell(|| "table value", value_table, 0, || Value::known(F::ZERO))?;
            offset += 1;

            for bit_size in bit_sizes.iter() {
                assert!(*bit_size < F::S as usize - 3);
                let table_values: Vec<F> = (0..1 << *bit_size).map(|e| F::from(e)).collect();
                for value in table_values.iter() {
                    table.assign_cell(
                        || "table tag",
                        tag_table,
                        offset,
                        || Value::known(F::from(*bit_size as u64 + 1)),
                    )?;
                    table.assign_cell(
                        || "table value",
                        value_table,
                        offset,
                        || Value::known(*value),
                    )?;
                    offset += 1;
                }
            }

            Ok(())
        },
    )?;

    Ok(())
}
