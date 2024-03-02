use ark_std::{end_timer, start_timer, Zero};
use circuitry::{
    chip::first_degree::FirstDegreeChip,
    gates::{range::RangeGate, vanilla::VanillaGate, vertical::VerticalGate},
    stack::Stack,
    LayoutCtx,
};
use ff::Field;
use halo2::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    halo2curves::bn256::{Fr, G1Affine, G2Affine},
    plonk::{Circuit, ConstraintSystem, Error},
};
use integer::rns::Rns;
use rand_core::OsRng;

use crate::PairingChip;

fn make_stack(n: usize) -> Stack<Fr> {
    assert!(!n.is_zero());
    let mut acc = Fr::ZERO;
    let n = 2;

    let mut g1: Vec<G1Affine> = vec![];
    let mut g2: Vec<G2Affine> = vec![];

    for _ in 0..n - 1 {
        let s1 = Fr::random(OsRng);
        let s2 = Fr::random(OsRng);
        acc += s1 * s2;
        g1.push((G1Affine::generator() * s1).into());
        g2.push((G2Affine::generator() * s2).into());
    }

    g1.push((G1Affine::generator() * -acc).into());
    g2.push(G2Affine::generator());

    let rns: Rns<_, Fr, 3, 90> = Rns::construct();
    let ch: PairingChip<Fr, 3, 90, 18> = PairingChip::new(&rns);

    let stack = &mut Stack::default();
    let g1 = g1
        .iter()
        .map(|g1| ch.assign_point1(stack, Value::known(*g1)))
        .collect::<Vec<_>>();

    let g2 = g2
        .iter()
        .map(|g2| ch.assign_point2(stack, Value::known(*g2)))
        .collect::<Vec<_>>();

    let res = ch.pairing_check(stack, g1, g2);
    stack.assert_one(&res);

    stack.clone()
}

#[derive(Clone)]
struct TestConfig<
    const RANGE_W: usize,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const SUBLIMB_SIZE: usize,
> {
    vertical_gate: VerticalGate<RANGE_W>,
    vanilla_gate: VanillaGate,
    range_gate: RangeGate,
    stack: Stack<Fr>,
}

#[derive(Default, Clone)]
struct Params {
    n: usize,
}

#[derive(Default)]
struct TestCircuit<
    const RANGE_W: usize,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const SUBLIMB_SIZE: usize,
> {
    params: Params,
}

impl<
        const RANGE_W: usize,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    > Circuit<Fr> for TestCircuit<RANGE_W, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>
{
    type Config = TestConfig<RANGE_W, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = Params;

    fn configure_with_params(
        meta: &mut ConstraintSystem<Fr>,
        params: Self::Params,
    ) -> Self::Config {
        let advices = (0..RANGE_W)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>();

        let range_gate = RangeGate::configure(meta, &advices[..]);
        let vertical_gate = VerticalGate::configure(meta, &range_gate, advices.try_into().unwrap());
        let vanilla_gate = VanillaGate::configure(meta);

        let t0 = start_timer!(|| "witness gen");
        let stack = make_stack(params.n);
        end_timer!(t0);

        Self::Config {
            stack,
            range_gate,
            vertical_gate,
            vanilla_gate,
        }
    }

    fn configure(_meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        unreachable!();
    }

    fn without_witnesses(&self) -> Self {
        Self {
            params: self.params.clone(),
        }
    }

    fn synthesize(&self, mut cfg: Self::Config, ly: impl Layouter<Fr>) -> Result<(), Error> {
        let ly_ctx = &mut LayoutCtx::new(ly);

        let t0 = start_timer!(|| "layout");

        cfg.stack.layout_range_limbs(ly_ctx, &cfg.vertical_gate)?;
        cfg.stack.layout_range_single(ly_ctx, &cfg.vertical_gate)?;
        cfg.stack.layout_range_tables(ly_ctx, &cfg.range_gate)?;
        cfg.stack.layout_first_degree(ly_ctx, &cfg.vanilla_gate)?;
        cfg.stack.layout_second_degree(ly_ctx, &cfg.vanilla_gate)?;
        cfg.stack.apply_indirect_copy(ly_ctx)?;

        end_timer!(t0);

        Ok(())
    }

    fn params(&self) -> Self::Params {
        self.params.clone()
    }
}

fn run_test<
    const RANGE_W: usize,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const SUBLIMB_SIZE: usize,
>(
    n: usize,
    k: u32,
) {
    let params = Params { n };
    let circuit = TestCircuit::<RANGE_W, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE> { params };
    let public_inputs = vec![];
    let prover = match MockProver::run(k, &circuit, public_inputs) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#}"),
    };
    prover.assert_satisfied();
}

#[test]
fn test_pairing() {
    run_test::<
        2,
        3,  // number of limbs
        90, // limb size
        18, // sublimb size
    >(2, 21);
}
