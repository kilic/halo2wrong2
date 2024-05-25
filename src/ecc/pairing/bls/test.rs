use super::BLSPairingChip;
use crate::circuitry::{
    gates::{range::RangeGate, vanilla::VanillaGate, vertical::VerticalGate},
    stack::Stack,
    LayoutCtx,
};
use crate::integer::rns::Rns;
use ark_std::{end_timer, start_timer, Zero};
use ff::Field;
use halo2::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    halo2curves::bls12381::{Fr, G1Affine, G2Affine},
    plonk::{Circuit, ConstraintSystem, Error},
};

fn make_stack(n: usize, limb_size: usize, sublimb_size: usize) -> Stack<Fr> {
    assert!(!n.is_zero());

    let g1 = G1Affine::generator();
    let g2 = G2Affine::generator();

    use group::Curve;
    let a1 = Fr::from(3u64);
    let a2 = Fr::from(5u64);
    let b1 = Fr::from(1u64);
    let b2 = a1 * a2 * b1.invert().unwrap().neg();
    let a1 = (g1 * a1).to_affine();
    let a2 = (g2 * a2).to_affine();
    let b1 = (g1 * b1).to_affine();
    let b2 = (g2 * b2).to_affine();

    let g1 = vec![a1, b1];
    let g2 = vec![a2, b2];

    let rns: Rns<_, Fr> = Rns::construct(limb_size);
    let ch: BLSPairingChip<Fr> = BLSPairingChip::new(&rns, sublimb_size);

    let stack = &mut Stack::default();
    let g1 = g1
        .iter()
        .map(|g1| ch.assign_point1(stack, Value::known(*g1)))
        .collect::<Vec<_>>();

    let g2 = g2
        .iter()
        .map(|g2| ch.assign_point2(stack, Value::known(*g2)))
        .collect::<Vec<_>>();

    let _ = ch.miller_loop(stack, &g1[..], &g2[..]);

    // println!("{:#?}", f.value());

    stack.clone()
}

#[derive(Clone)]
struct TestConfig<const RANGE_W: usize> {
    vertical_gate: VerticalGate<RANGE_W>,
    vanilla_gate: VanillaGate,
    range_gate: RangeGate,
    stack: Stack<Fr>,
}

#[derive(Default, Clone)]
struct Params {
    n: usize,
    limb_size: usize,
    sublimb_size: usize,
}

#[derive(Default)]
struct TestCircuit<const RANGE_W: usize> {
    params: Params,
}

impl<const RANGE_W: usize> Circuit<Fr> for TestCircuit<RANGE_W> {
    type Config = TestConfig<RANGE_W>;
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
        let stack = make_stack(params.n, params.limb_size, params.sublimb_size);
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

fn run_test<const RANGE_W: usize>(k: u32, limb_size: usize, sublimb_size: usize, n: usize) {
    let params = Params {
        n,
        limb_size,
        sublimb_size,
    };
    let circuit = TestCircuit::<RANGE_W> { params };
    let public_inputs = vec![];
    let prover = match MockProver::run(k, &circuit, public_inputs) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#}"),
    };
    prover.assert_satisfied();
}

#[test]
fn test_bls_pairing_check() {
    run_test::<2>(21, 80, 16, 2);
}
