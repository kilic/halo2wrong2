use super::{rand_arithmetic, rand_stack_first_degree, rand_stack_second_degree, run_test};
use crate::circuitry::{gates::vanilla::VanillaGate, stack::Stack, LayoutCtx};
use ff::PrimeField;
use halo2::{
    circuit::{Layouter, SimpleFloorPlanner},
    halo2curves::pasta::Fp,
    plonk::{Circuit, ConstraintSystem, Error},
};

mod composition {

    use std::marker::PhantomData;

    use super::*;
    #[derive(Clone)]
    struct Config<F: PrimeField + Ord> {
        vanilla_gate: VanillaGate,
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

            let mut stack = Stack::default();
            rand_stack_first_degree::<_>(&mut stack, true);
            rand_stack_second_degree::<_>(&mut stack);
            Self::Config {
                vanilla_gate,
                stack,
            }
        }

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn synthesize(&self, mut cfg: Self::Config, ly: impl Layouter<F>) -> Result<(), Error> {
            let ly = &mut LayoutCtx::new(ly);

            cfg.stack.layout_first_degree(ly, &cfg.vanilla_gate)?;
            cfg.stack.layout_second_degree(ly, &cfg.vanilla_gate)?;
            cfg.stack.apply_indirect_copy(ly)?;
            Ok(())
        }
    }

    #[test]
    fn test_vanilla_composision() {
        let circuit = TestCircuit::<Fp>::default();
        run_test(17, &circuit);
    }
}

mod arithmetic {
    use std::marker::PhantomData;

    use crate::circuitry::gates::select::SelectGate;

    use super::*;

    #[derive(Clone)]
    struct Config<F: PrimeField + Ord> {
        vanilla_gate: VanillaGate,
        select_gate: SelectGate,
        stack: Stack<F>,
    }

    #[derive(Clone, Default)]
    struct TestCircuit<F: PrimeField + Ord>(PhantomData<F>);

    impl<F: PrimeField + Ord> Circuit<F> for TestCircuit<F> {
        type Params = ();
        type Config = Config<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let stack = rand_arithmetic::<_>();
            let vanilla_gate = VanillaGate::configure(meta);
            let shared_advices = vanilla_gate.advice_colums();
            let extra_advice = meta.advice_column();
            let select_gate = SelectGate::configure(
                meta,
                shared_advices[0],
                shared_advices[1],
                shared_advices[2],
                extra_advice,
            );

            Self::Config {
                stack,
                vanilla_gate,
                select_gate,
            }
        }

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn synthesize(&self, mut cfg: Self::Config, ly: impl Layouter<F>) -> Result<(), Error> {
            let ly = &mut LayoutCtx::new(ly);
            cfg.stack.layout_first_degree(ly, &cfg.vanilla_gate)?;
            cfg.stack.layout_second_degree(ly, &cfg.vanilla_gate)?;
            cfg.stack.layout_selections(ly, &cfg.select_gate)?;
            cfg.stack.apply_indirect_copy(ly)?;
            Ok(())
        }

        fn params(&self) -> Self::Params {}
    }

    #[test]
    fn test_vanilla_arithmetic() {
        let circuit = TestCircuit::<Fp>::default();
        run_test(17, &circuit);
    }
}
