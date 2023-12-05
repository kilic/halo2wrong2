use std::marker::PhantomData;

use ff::PrimeField;

use halo2::{
    circuit::{Layouter, SimpleFloorPlanner},
    halo2curves::pasta::Fp,
    plonk::{Circuit, ConstraintSystem, Error},
};

use crate::{
    chip::ROMChip,
    gates::{rom::ROMGate, vanilla::VanillaGate},
};
use crate::{stack::Stack, LayoutCtx};

use super::*;

fn make_stack<F: PrimeField + Ord>(rom_size: usize) -> Stack<F> {
    let mut stack: Stack<F> = Stack::with_rom(rom_size);

    let tag = F::random(OsRng);

    let w0 = (0..rom_size)
        .map(|_| stack.assign_rand_witness())
        .collect::<Vec<_>>();

    let w1 = (0..rom_size)
        .map(|_| stack.assign_rand_witness())
        .collect::<Vec<_>>();

    let w2 = (0..rom_size)
        .map(|_| stack.assign_rand_witness())
        .collect::<Vec<_>>();

    let w3 = (0..rom_size)
        .map(|_| stack.assign_rand_witness())
        .collect::<Vec<_>>();

    let a0 = F::from(0);
    let a1 = F::from(1);
    let a2 = F::from(2);
    let a3 = F::from(3);

    stack.write(tag, a0, &w0);
    stack.write(tag, a1, &w1);
    stack.write(tag, a2, &w2);
    stack.write(tag, a3, &w3);

    let f0 = &stack.assign(v!(F::from(0)));
    let f1 = &stack.assign(v!(F::from(1)));
    let f2 = &stack.assign(v!(F::from(2)));
    let f3 = &stack.assign(v!(F::from(3)));

    let _w1 = stack.read(tag, F::ZERO, f1);
    w1.iter().zip(_w1.iter()).for_each(|(w, a)| {
        stack.equal(w, a);
    });
    let _w0 = stack.read(tag, F::ZERO, f0);
    w0.iter().zip(_w0.iter()).for_each(|(w, a)| {
        stack.equal(w, a);
    });
    let _w3 = stack.read(tag, F::ZERO, f3);
    w3.iter().zip(_w3.iter()).for_each(|(w, a)| {
        stack.equal(w, a);
    });
    let _w3 = stack.read(tag, F::ZERO, f3);
    w3.iter().zip(_w3.iter()).for_each(|(w, a)| {
        stack.equal(w, a);
    });
    let _w0 = stack.read(tag, F::ZERO, f0);
    w0.iter().zip(_w0.iter()).for_each(|(w, a)| {
        stack.equal(w, a);
    });
    let _w2 = stack.read(tag, F::ZERO, f2);
    w2.iter().zip(_w2.iter()).for_each(|(w, a)| {
        stack.equal(w, a);
    });
    let _w2 = stack.read(tag, F::ZERO, f2);
    w2.iter().zip(_w2.iter()).for_each(|(w, a)| {
        stack.equal(w, a);
    });

    stack
}

#[derive(Clone)]
struct Config<F: PrimeField + Ord> {
    vanilla_gate: VanillaGate,
    rom_gate: ROMGate,
    stack: Stack<F>,
}

#[derive(Clone, Default)]
struct TestCircuit<F: PrimeField + Ord>(PhantomData<F>);

impl<F: PrimeField + Ord> Circuit<F> for TestCircuit<F> {
    type Params = ();
    type Config = Config<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let vanilla_gate = VanillaGate::configure(meta);
        let query_values = vanilla_gate.advice_colums();
        let table_values = query_values;
        let query_fraction = meta.advice_column();

        let rom_gate = ROMGate::configure(meta, query_fraction, &query_values, &table_values);
        let stack = make_stack::<_>(3);

        Self::Config {
            stack,
            vanilla_gate,
            rom_gate,
        }
    }

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn synthesize(&self, mut cfg: Self::Config, ly: impl Layouter<F>) -> Result<(), Error> {
        let ly = &mut LayoutCtx::new(ly);
        cfg.stack.layout_first_degree(ly, &cfg.vanilla_gate)?;
        cfg.stack.layout_second_degree(ly, &cfg.vanilla_gate)?;
        cfg.stack.layout_rom(ly, &cfg.rom_gate)?;
        cfg.stack.apply_indirect_copy(ly)?;
        Ok(())
    }
}

#[test]
fn test_rom_gate() {
    let circuit = TestCircuit::<Fp>::default();
    run_test(12, &circuit);
}
