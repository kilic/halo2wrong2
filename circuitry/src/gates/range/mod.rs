use std::collections::BTreeMap;

use ff::PrimeField;
use halo2_pse::{
    circuit::{Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, TableColumn},
};

use crate::{witness::Witness, LayoutCtx, RegionCtx};

pub mod in_place;
pub mod in_place_sparse;

pub trait RangeInPlace<F: PrimeField, const W: usize>: RangeTableLayout<F> + Clone {
    fn configure(meta: &mut ConstraintSystem<F>, values: [Column<Advice>; W]) -> Self;

    fn enable(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        idx: usize,
        bit_size: usize,
    ) -> Result<(), Error>;

    fn assign_remainings(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        ranges: &[Witness<F>],
        values: [Column<Advice>; W],
    ) -> Result<(), Error>;
}

pub trait RangeTableLayout<F: PrimeField> {
    fn layout_range_tables<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        bit_sizes: &[usize],
    ) -> Result<(), Error>;
}

pub fn sort_by_size<F: PrimeField>(
    witnesses: &[Witness<F>],
    exclude: Option<usize>,
) -> BTreeMap<usize, Vec<Witness<F>>> {
    let mut sorted = BTreeMap::<usize, Vec<Witness<F>>>::new();

    for witness in witnesses.iter() {
        let bit_size = witness.range.expect("not a range enforcement");
        if let Some(exclude) = exclude {
            if exclude == bit_size {
                continue;
            }
        }
        assert!(bit_size > 0);

        sorted
            .entry(bit_size)
            .and_modify(|witnesses| witnesses.push(*witness))
            .or_insert_with(|| vec![*witness]);
    }

    sorted
}

pub fn range_sizes<F: PrimeField>(witnesses: &[Witness<F>]) -> Vec<usize> {
    let sorted = sort_by_size(witnesses, None);
    let mut tables: Vec<_> = sorted.keys().copied().collect();
    tables.sort();
    tables
}

pub(crate) fn layout_range_table<F: PrimeField, L: Layouter<F>>(
    ly_ctx: &mut LayoutCtx<F, L>,
    value_table: TableColumn,
    bit_size: usize,
) -> Result<(), Error> {
    ly_ctx.layouter.assign_table(
        || "",
        |mut table| {
            let mut offset = 0;
            let table_values: Vec<F> = (0..1 << bit_size).map(|e| F::from(e)).collect();
            for value in table_values.iter() {
                table.assign_cell(
                    || "table value",
                    value_table,
                    offset,
                    || Value::known(*value),
                )?;
                offset += 1;
            }
            Ok(())
        },
    )?;

    Ok(())
}

pub(crate) fn layout_tagged_range_tables<F: PrimeField, L: Layouter<F>>(
    ly_ctx: &mut LayoutCtx<F, L>,
    tag_table: TableColumn,
    value_table: TableColumn,
    bit_sizes: &[usize],
) -> Result<(), Error> {
    ly_ctx.layouter.assign_table(
        || "",
        |mut table| {
            let mut offset = 0;

            table.assign_cell(|| "table tag", tag_table, 0, || Value::known(F::ZERO))?;
            table.assign_cell(|| "table value", value_table, 0, || Value::known(F::ZERO))?;
            offset += 1;

            for bit_size in bit_sizes {
                assert!(*bit_size < F::S as usize - 3);
                let table_values: Vec<F> = (0..1 << bit_size).map(|e| F::from(e)).collect();
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
