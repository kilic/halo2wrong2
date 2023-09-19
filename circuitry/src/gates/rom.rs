use std::marker::PhantomData;

use ff::PrimeField;
use halo2::{
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector},
    poly::Rotation,
};

use crate::{
    enforcement::MemoryOperation,
    witness::{Composable, Witness},
    LayoutCtx, RegionCtx,
};

use super::GateLayout;

#[derive(Clone, Debug)]
pub struct ROMGate<F: PrimeField, const W: usize> {
    pub(crate) query_selector: Selector,
    pub(crate) query_tag: Column<Fixed>,
    pub(crate) query_fraction: Column<Advice>,
    pub(crate) query_base: Column<Fixed>,
    pub(crate) query: [Column<Advice>; W],

    pub(crate) table_tag: Column<Fixed>,
    pub(crate) table_address: Column<Fixed>,
    pub(crate) table: [Column<Advice>; W],

    pub(crate) _marker: PhantomData<F>,
}

impl<F: PrimeField + Ord, const W: usize> ROMGate<F, W> {
    pub fn configure(
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

            let argument = query
                .into_iter()
                .zip(table.into_iter())
                .chain(std::iter::once((
                    query_fraction + query_base,
                    table_address,
                )))
                .chain(std::iter::once((query_tag, table_tag)))
                .map(|(query, table)| (query_selector.clone() * query, table)) //
                .collect::<Vec<_>>();

            argument
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

            _marker: PhantomData,
        }
    }
}

impl<F: PrimeField + Ord, const W: usize> GateLayout<F, Vec<MemoryOperation<F, W>>>
    for ROMGate<F, W>
{
    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<MemoryOperation<F, W>>,
    ) -> Result<(), Error> {
        #[cfg(feature = "info")]
        {
            println!("---");
            println!("ROM gate");
            let mut n_write = 0;
            let mut n_read = 0;
            for e in e.iter() {
                match e {
                    MemoryOperation::Write { .. } => n_write += 1,
                    MemoryOperation::Read { .. } => n_read += 1,
                }
            }
            println!("* * n_write: {}", n_write);
            println!("* * n_read: {}", n_read);
            println!();
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut crate::RegionCtx::new(region, &mut ly_ctx.cell_map);

                for op in e.iter() {
                    match op {
                        MemoryOperation::Write {
                            tag,
                            address,
                            values,
                        } => {
                            self.write(ctx, *tag, *address, values)?;
                        }
                        MemoryOperation::Read {
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

        Ok(())
    }
}

impl<F: PrimeField + Ord, const W: usize> ROMGate<F, W> {
    fn read(
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
        ctx.fixed(self.table_tag, F::zero())?;
        ctx.fixed(self.table_address, F::zero())?;

        ctx.enable(self.query_selector)?;
        ctx.next(); // TODO consider not to go next
        Ok(())
    }

    fn write(
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

#[cfg(test)]
mod test {
    use std::collections::BTreeMap;

    use super::*;

    use halo2::{
        circuit::{SimpleFloorPlanner, Value},
        dev::MockProver,
        halo2curves::{pasta::Fp, FieldExt},
        plonk::Circuit,
    };
    use rand_core::OsRng;

    macro_rules! v {
        ($e:expr) => {
            Value::known($e)
        };
    }

    pub fn rand_value<F: PrimeField>() -> Value<F> {
        let value = F::random(OsRng);
        v!(value)
    }

    #[derive(Clone)]
    struct TestConfig<F: PrimeField + Ord, const W: usize> {
        rom_gate: ROMGate<F, W>,
    }

    struct TestCircuit<F: PrimeField + Ord, const W: usize> {
        _marker: PhantomData<F>,
    }

    impl<F: PrimeField + Ord, const W: usize> Circuit<F> for TestCircuit<F, W> {
        type Config = TestConfig<F, W>;
        type FloorPlanner = SimpleFloorPlanner;

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let values = (0..W).map(|_| meta.advice_column()).collect::<Vec<_>>();

            let table_values = values.clone();
            let query_values = values.clone();
            let query_fraction = meta.advice_column();
            let rom_gate = ROMGate::configure(
                meta,
                query_fraction,
                query_values.try_into().unwrap(),
                table_values.try_into().unwrap(),
            );

            Self::Config { rom_gate }
        }

        fn without_witnesses(&self) -> Self {
            Self {
                _marker: PhantomData,
            }
        }

        fn synthesize(&self, cfg: Self::Config, mut ly: impl Layouter<F>) -> Result<(), Error> {
            let _offset = ly.assign_region(
                || "",
                |region| {
                    let cell_map = &mut BTreeMap::new();
                    let ctx = &mut crate::RegionCtx::new(region, cell_map);

                    // lets fill some random values first
                    for _ in 0..10 {
                        let values = [rand_value::<F>(); W];
                        for (value, column) in values.iter().zip(cfg.rom_gate.query.iter()) {
                            let _new_cell = ctx.advice(*column, *value)?;
                        }
                        ctx.fixed(cfg.rom_gate.table_address, F::zero())?;
                        ctx.fixed(cfg.rom_gate.table_tag, F::zero())?;
                        ctx.fixed(cfg.rom_gate.query_base, F::zero())?;
                        ctx.fixed(cfg.rom_gate.query_tag, F::zero())?;
                        ctx.next();
                    }

                    let magic = F::from(333);

                    let addresses = [101u64, 102, 103, 104];
                    let addresses = addresses.into_iter().map(F::from).collect::<Vec<_>>();
                    let table = addresses
                        .iter()
                        .map(|address| {
                            let values = [rand_value::<F>(); W];
                            for (value, column) in values.iter().zip(cfg.rom_gate.query.iter()) {
                                let _new_cell = ctx.advice(*column, *value)?;
                            }
                            ctx.fixed(cfg.rom_gate.table_address, *address)?;
                            ctx.fixed(cfg.rom_gate.table_tag, magic)?;
                            ctx.fixed(cfg.rom_gate.query_base, F::zero())?;
                            ctx.fixed(cfg.rom_gate.query_tag, F::zero())?;
                            ctx.next();

                            Ok(values)
                        })
                        .collect::<Result<Vec<_>, Error>>()?;

                    for _ in 0..10 {
                        let values = [rand_value::<F>(); W];
                        for (value, column) in values.iter().zip(cfg.rom_gate.query.iter()) {
                            let _new_cell = ctx.advice(*column, *value)?;
                        }
                        // ctx.advice(cfg.rom_gate.query_fraction, Value::known(F::one()))?;
                        ctx.advice(cfg.rom_gate.query_fraction, Value::known(F::one()))?;
                        ctx.fixed(cfg.rom_gate.table_address, F::zero())?;
                        ctx.fixed(cfg.rom_gate.table_tag, F::zero())?;
                        ctx.fixed(cfg.rom_gate.query_base, F::zero())?;
                        ctx.fixed(cfg.rom_gate.query_tag, F::zero())?;
                        // ctx.enable(cfg.rom_gate.query_selector)?;
                        ctx.next();
                    }

                    // lets make a query

                    let address = addresses[2];
                    let values = table[2];

                    for (value, column) in values.iter().zip(cfg.rom_gate.query.iter()) {
                        let _new_cell = ctx.advice(*column, *value)?;
                    }
                    ctx.fixed(cfg.rom_gate.query_base, F::zero())?;

                    ctx.advice(cfg.rom_gate.query_fraction, Value::known(address))?;
                    ctx.fixed(cfg.rom_gate.query_tag, magic)?;

                    ctx.fixed(cfg.rom_gate.table_address, F::from(103))?;
                    ctx.fixed(cfg.rom_gate.table_tag, magic)?;

                    ctx.enable(cfg.rom_gate.query_selector)?;
                    ctx.next();

                    // for op in e.iter() {
                    //     match op {
                    //         MemoryOperation::Write { address, values } => {
                    //             self.write(ctx, *address, values)?;
                    //         }
                    //         MemoryOperation::Read {
                    //             base,
                    //             fraction,
                    //             values,
                    //         } => {
                    //             self.read(ctx, *base, fraction, values)?;
                    //         }
                    //     }
                    // }

                    Ok(ctx.offset())
                },
            )?;

            println!("offset: {:#?}", _offset);
            Ok(())
        }
    }

    fn run_test_rom<F: FieldExt, const W: usize>() {
        const K: u32 = 17;
        let circuit = TestCircuit::<F, W> {
            _marker: PhantomData::<F>,
        };
        let public_inputs: Vec<Vec<F>> = vec![];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };

        prover.assert_satisfied();
    }

    #[test]
    fn test_xxx() {
        run_test_rom::<Fp, 1>();
    }
}
