use ff::PrimeField;
use std::marker::PhantomData;

use halo2::{
    circuit::{Layouter, SimpleFloorPlanner},
    halo2curves::pasta::Fp,
    plonk::{Circuit, ConstraintSystem, Error},
};

use crate::{
    gates::{range::RangeGate, vertical::VerticalGate},
    stack::Stack,
    LayoutCtx,
};

use super::{rand_stack_range, run_test};

mod range {
    use super::*;

    #[derive(Clone)]
    struct Config<F: PrimeField + Ord, const W: usize> {
        vertical_gate: VerticalGate<W>,
        stack: Stack<F, 0>,
    }

    #[derive(Clone, Default)]
    struct TestCircuit<F: PrimeField + Ord, const W: usize>(PhantomData<F>);

    impl<F: PrimeField + Ord, const W: usize> Circuit<F> for TestCircuit<F, W> {
        type Params = ();
        type Config = Config<F, W>;
        type FloorPlanner = SimpleFloorPlanner;

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advices = (0..W).map(|_| meta.advice_column()).collect::<Vec<_>>();

            let range_gate = RangeGate::configure(meta, &advices[..]);
            let vertical_gate =
                VerticalGate::configure(meta, &range_gate, advices.try_into().unwrap());

            let mut stack: Stack<F, 0> = Stack::default();
            rand_stack_range::<_>(&mut stack);

            Self::Config {
                stack,
                vertical_gate,
            }
        }

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn synthesize(&self, mut cfg: Self::Config, ly: impl Layouter<F>) -> Result<(), Error> {
            let ly = &mut LayoutCtx::new(ly);
            cfg.stack.layout_range_limbs(ly, &cfg.vertical_gate)?;
            cfg.stack.layout_range_single(ly, &cfg.vertical_gate)?;
            cfg.stack
                .layout_range_tables(ly, &cfg.vertical_gate.range_gate)?;
            cfg.stack.apply_indirect_copy(ly)?;
            Ok(())
        }
    }

    #[test]
    fn test_vertical_gate_decomposition() {
        let circuit = TestCircuit::<Fp, 2>::default();
        run_test(17, &circuit);
    }
}

mod composition {
    use crate::test::rand_stack_first_degree;

    use super::*;

    #[derive(Clone)]
    struct Config<F: PrimeField + Ord> {
        stack: Stack<F, 0>,
        vertical_gate: VerticalGate<1>,
    }

    #[derive(Clone, Default)]
    struct TestCircuit<F: PrimeField + Ord>(PhantomData<F>);

    impl<F: PrimeField + Ord> Circuit<F> for TestCircuit<F> {
        type Params = ();
        type Config = Config<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice = meta.advice_column();

            let range_gate = RangeGate::configure(meta, &[advice]);
            let vertical_gate = VerticalGate::configure(meta, &range_gate, [advice]);
            let mut stack: Stack<_, 0> = Stack::default();
            rand_stack_first_degree::<_>(&mut stack, false);

            Self::Config {
                stack,
                vertical_gate,
            }
        }

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn synthesize(&self, mut cfg: Self::Config, ly: impl Layouter<F>) -> Result<(), Error> {
            let ly = &mut LayoutCtx::new(ly);
            cfg.stack.layout_first_degree(ly, &cfg.vertical_gate)?;
            cfg.stack.apply_indirect_copy(ly)?;
            Ok(())
        }
    }

    #[test]
    fn test_vertical_gate_composition() {
        let circuit = TestCircuit::<Fp>::default();
        run_test(17, &circuit);
    }
}
