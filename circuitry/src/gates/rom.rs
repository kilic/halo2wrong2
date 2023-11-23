use ff::PrimeField;
use halo2::{
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector},
    poly::Rotation,
};

use crate::{
    witness::{Composable, Witness},
    LayoutCtx, RegionCtx,
};

use super::GateLayout;

#[derive(Clone, Debug)]
pub struct ROMGate<const W: usize> {
    pub(crate) query_selector: Selector,
    pub(crate) query_tag: Column<Fixed>,
    pub(crate) query_fraction: Column<Advice>,
    pub(crate) query_base: Column<Fixed>,
    pub(crate) query: [Column<Advice>; W],

    pub(crate) table_tag: Column<Fixed>,
    pub(crate) table_address: Column<Fixed>,
    pub(crate) table: [Column<Advice>; W],
}

impl<const W: usize> ROMGate<W> {
    pub fn configure<F: PrimeField>(
        meta: &mut ConstraintSystem<F>,
        query_fraction: Column<Advice>,
        query: [Column<Advice>; W],
        table: [Column<Advice>; W],
    ) -> Self {
        let query_tag = meta.fixed_column();
        let table_tag = meta.fixed_column();
        let table_address = meta.fixed_column();
        let query_base = meta.fixed_column();
        let query_selector = meta.complex_selector();

        meta.enable_equality(query_fraction);

        for table in table.iter() {
            meta.enable_equality(*table);
        }

        for query in query.iter() {
            meta.enable_equality(*query);
        }

        meta.lookup_any("windowed point table", |meta| {
            let table_address = meta.query_fixed(table_address, Rotation::cur());
            let table_tag = meta.query_fixed(table_tag, Rotation::cur());
            let table: Vec<_> = table
                .iter()
                .map(|table| meta.query_advice(*table, Rotation::cur()))
                .collect();

            let query_fraction = meta.query_advice(query_fraction, Rotation::cur());
            let query_base = meta.query_fixed(query_base, Rotation::cur());
            let query_tag = meta.query_fixed(query_tag, Rotation::cur());
            let query: Vec<_> = query
                .iter()
                .map(|query| meta.query_advice(*query, Rotation::cur()))
                .collect();

            let query_selector = meta.query_selector(query_selector);

            query
                .into_iter()
                .zip(table)
                .chain(std::iter::once((query_fraction + query_base, table_address)))
                .chain(std::iter::once((query_tag, table_tag)))
                .map(|(query, table)| (query_selector.clone() * query, table)) //
                .collect::<Vec<_>>()
        });

        Self {
            query_selector,
            query_tag,
            query_base,
            query_fraction,
            query,

            table_tag,
            table_address,
            table,
        }
    }
}

impl<F: PrimeField + Ord, const W: usize> GateLayout<F, Vec<crate::enforcement::ROM<F, W>>>
    for ROMGate<W>
{
    type Output = ();

    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<crate::enforcement::ROM<F, W>>,
    ) -> Result<(), Error> {
        #[cfg(feature = "info")]
        {
            println!("---");
            let mut n_write = 0;
            let mut n_read = 0;
            for e in e.iter() {
                match e {
                    crate::enforcement::ROM::Write { .. } => n_write += 1,
                    crate::enforcement::ROM::Read { .. } => n_read += 1,
                }
            }
            println!("* n_write: {n_write}");
            println!("* n_read: {n_read}");
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut crate::RegionCtx::new(region, &mut ly_ctx.cell_map);

                for op in e.iter() {
                    match op {
                        crate::enforcement::ROM::Write {
                            tag,
                            address,
                            values,
                        } => {
                            self.write(ctx, *tag, *address, values)?;
                        }
                        crate::enforcement::ROM::Read {
                            tag,
                            address_base,
                            address_fraction,
                            values,
                        } => {
                            self.read(ctx, *tag, *address_base, address_fraction, values)?;
                        }
                    }
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

impl<const W: usize> ROMGate<W> {
    fn read<F: PrimeField>(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        tag: F,
        address_base: F,
        address_fraction: &Witness<F>,
        values: &[Witness<F>; W],
    ) -> Result<(), Error> {
        // println!("READ");
        // println!("base: {:?}", base);
        // println!("fraction: {:?}", fraction.value());
        // println!(
        // "values: {:#?}",
        // values.iter().map(|v| v.value()).collect::<Vec<_>>()
        // );
        let _ = values
            .iter()
            .zip(self.query.into_iter())
            .map(|(limb, column)| {
                let new_cell = ctx.advice(column, limb.value())?;
                if let Some(id) = limb.id {
                    ctx.copy_chain(id, new_cell)?;
                }

                Ok(())
            })
            .collect::<Result<Vec<_>, Error>>()?;
        ctx.fixed(self.query_base, address_base)?;
        let new_cell = ctx.advice(self.query_fraction, address_fraction.value())?;
        if let Some(id) = address_fraction.id {
            ctx.copy_chain(id, new_cell)?;
        }
        ctx.fixed(self.query_tag, tag)?;

        // just in case
        ctx.fixed(self.table_tag, F::ZERO)?;
        ctx.fixed(self.table_address, F::ZERO)?;

        ctx.enable(self.query_selector)?;
        ctx.next(); // TODO consider not to go next
        Ok(())
    }

    fn write<F: PrimeField>(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        tag: F,
        address: F,
        values: &[Witness<F>; W],
    ) -> Result<(), Error> {
        // println!("WRITE");
        // println!("address: {:?}", address);
        // println!(
        //     "values: {:#?}",
        //     values.iter().map(|v| v.value()).collect::<Vec<_>>()
        // );
        let _ = values
            .iter()
            .zip(self.table.into_iter())
            .map(|(limb, column)| {
                let new_cell = ctx.advice(column, limb.value())?;
                if let Some(id) = limb.id {
                    ctx.copy_chain(id, new_cell)?;
                }
                Ok(())
            })
            .collect::<Result<Vec<_>, Error>>()?;
        ctx.fixed(self.table_address, address)?;
        ctx.fixed(self.table_tag, tag)?;
        ctx.next();
        Ok(())
    }
}
