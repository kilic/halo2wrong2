use ark_std::end_timer;
use ark_std::start_timer;
use circuitry::gates::range::RangeGate;
use circuitry::gates::rom::ROMGate;
use circuitry::gates::vanilla::VanillaGate;
use circuitry::gates::vertical::VerticalGate;
use circuitry::stack::Stack;
use ff::Field;
use ff::FromUniformBytes;
use group::{Curve, Group};
use halo2::halo2curves::bn256::{G1Affine, G1};
use halo2::halo2curves::CurveExt;
use halo2::plonk::{Advice, Column};
use halo2::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    halo2curves::CurveAffine,
    plonk::{Circuit, ConstraintSystem, Error},
};

use integer::rns::Rns;

use circuitry::witness::Witness;
use circuitry::LayoutCtx;
use rand_core::OsRng;

use crate::base_field_ecc::BaseFieldEccChip;
use crate::test::run_test_prover;
use crate::Point;

pub(crate) fn _multiexp_naive_var<C: CurveExt>(point: &[C], scalar: &[C::ScalarExt]) -> C {
    assert!(!point.is_empty());
    assert_eq!(point.len(), scalar.len());
    point
        .iter()
        .zip(scalar.iter())
        .fold(C::identity(), |acc, (point, scalar)| {
            acc + (*point * *scalar)
        })
}

fn make_stack<
    C: CurveAffine,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const SUBLIMB_SIZE: usize,
>(
    rns: &Rns<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
    witness_aux: Value<C>,
    constant_aux: C,
    window_size: usize,
    number_of_points: usize,
) -> Stack<C::Scalar> {
    let stack = &mut Stack::<C::Scalar>::with_rom(NUMBER_OF_LIMBS);

    let ch: BaseFieldEccChip<C, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE> =
        BaseFieldEccChip::new(rns, witness_aux, constant_aux);

    fn value<T>(e: T) -> Value<T> {
        Value::known(e)
    }

    // constant registry
    {
        let p = C::CurveExt::random(OsRng);
        let p_val = Value::known(p.into());
        let p_assigned = ch.assign_point(stack, p_val);
        let p_constant = ch.register_constant(stack, p.into());
        ch.assert_on_curve(stack, &p_constant);
        ch.copy_equal(stack, &p_assigned, &p_constant);
        ch.normal_equal(stack, &p_assigned, &p_constant);
    }

    // add
    {
        let a: Value<C> = value(C::CurveExt::random(OsRng).into());
        let b: Value<C> = value(C::CurveExt::random(OsRng).into());
        let c: Value<C> = (a + b).map(|p| p.to_affine());
        let a = ch.assign_point(stack, a);
        let b = ch.assign_point(stack, b);
        let c0 = ch.assign_point(stack, c);
        let c1 = ch.add_incomplete(stack, &a, &b);
        ch.normal_equal(stack, &c0, &c1);

        let a: Value<C> = value(C::CurveExt::random(OsRng).into());
        let b: Value<C> = value(C::CurveExt::random(OsRng).into());
        let c: Value<C> = (a - b).map(|p| p.to_affine());
        let a = ch.assign_point(stack, a);
        let b = ch.assign_point(stack, b);
        let c0 = ch.assign_point(stack, c);
        let c1 = ch.sub_incomplete(stack, &a, &b);
        ch.normal_equal(stack, &c0, &c1);

        let n = 10;
        let points: Vec<C::CurveExt> = (0..n).map(|_| C::CurveExt::random(OsRng)).collect();
        let sum = points
            .iter()
            .fold(C::CurveExt::identity(), |acc, p| acc + p);
        let u0 = ch.assign_point(stack, value(sum.into()));
        let points = points
            .into_iter()
            .map(|p| ch.assign_point(stack, value(p.to_affine())))
            .collect::<Vec<_>>();
        let u1 = ch.add_multi(stack, &points[..]);
        ch.normal_equal(stack, &u0, &u1);
    }

    // double
    {
        let a: Value<C> = value(C::CurveExt::random(OsRng).into());
        let c = (a + a).map(|p| p.to_affine());
        let a = ch.assign_point(stack, a);
        let c0 = ch.assign_point(stack, c);
        let c1 = ch.double_incomplete(stack, &a);
        ch.normal_equal(stack, &c0, &c1);
    }

    // mul var
    {
        let tag0 = C::Scalar::random(OsRng);
        // let tag1 = C::Scalar::random(OsRng);

        let points: Vec<C::CurveExt> = (0..number_of_points)
            .map(|_| C::CurveExt::random(OsRng))
            .collect();

        let scalars: Vec<C::Scalar> = (0..number_of_points)
            .map(|_| C::Scalar::random(OsRng))
            .collect();

        let res0 = _multiexp_naive_var(&points[..], &scalars[..]).to_affine();

        #[allow(clippy::type_complexity)]
        let (points, scalars): (
            Vec<Point<C::Base, C::ScalarExt, NUMBER_OF_LIMBS, LIMB_SIZE>>,
            Vec<Witness<C::ScalarExt>>,
        ) = points
            .into_iter()
            .zip(scalars)
            .map(|(point, scalar)| {
                let point = ch.assign_point(stack, value(point.into()));
                let scalar = ch.assign_scalar(stack, value(scalar));
                (point, scalar)
            })
            .unzip();

        let res1 = ch.msm_sliding_vertical_rom(stack, tag0, &points[..], &scalars[..], window_size);
        res1.value::<C>().map(|res1| assert_eq!(res0, res1));

        let res0 = ch.assign_point(stack, value(res0));
        ch.normal_equal(stack, &res0, &res1);
    }

    // mul fix
    {
        let point = C::CurveExt::random(OsRng);
        let prepared = ch.prepare_mul_fix(stack, point.into());

        let scalar = C::Scalar::random(OsRng);
        let res0 = _multiexp_naive_var(&[point], &[scalar]).to_affine();
        let scalar = ch.assign_scalar(stack, value(scalar));
        let res1 = ch.mul_fix(stack, &prepared, &scalar);
        res1.value::<C>().map(|res1| assert_eq!(res0, res1));
        let res1 = ch.mul_fix(stack, &prepared, &scalar);
        let res0 = ch.assign_point(stack, value(res0));
        ch.normal_equal(stack, &res0, &res1);
    }

    stack.clone()
}

#[derive(Clone)]
struct TestConfig<
    C: CurveAffine,
    const RANGE_W: usize,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const SUBLIMB_SIZE: usize,
> {
    vertical_gate: VerticalGate<RANGE_W>,
    vanilla_gate: VanillaGate,
    range_gate: RangeGate,
    rom_gate: ROMGate,
    stack: Stack<C::Scalar>,
}

#[derive(Default, Clone)]
struct Params<C: CurveAffine> {
    witness_aux: Value<C>,
    constant_aux: C,
    number_of_points: usize,
    window: usize,
}

#[derive(Default)]
struct TestCircuit<
    C: CurveAffine,
    const RANGE_W: usize,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const SUBLIMB_SIZE: usize,
> {
    params: Params<C>,
}

impl<
        C: CurveAffine,
        const RANGE_W: usize,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    > Circuit<C::Scalar> for TestCircuit<C, RANGE_W, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>
{
    type Config = TestConfig<C, RANGE_W, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = Params<C>;

    fn configure_with_params(
        meta: &mut ConstraintSystem<C::Scalar>,
        params: Self::Params,
    ) -> Self::Config {
        let advices = (0..RANGE_W)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>();

        let range_gate = RangeGate::configure(meta, &advices[..]);
        let vertical_gate = VerticalGate::configure(meta, &range_gate, advices.try_into().unwrap());
        let vanilla_gate = VanillaGate::configure(meta);

        let shared_columns = vanilla_gate.advice_colums();
        let rom_value_columns: [Column<Advice>; NUMBER_OF_LIMBS] =
            shared_columns[0..NUMBER_OF_LIMBS].try_into().unwrap();
        let query_fraction = vertical_gate.advice_columns()[0];

        let rom_gate = ROMGate::configure(
            meta,
            query_fraction,
            &rom_value_columns[..],
            &rom_value_columns[..],
        );

        let rns = Rns::construct();

        let t0 = start_timer!(|| "witness gen");
        let stack = make_stack::<C, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>(
            &rns,
            params.witness_aux,
            params.constant_aux,
            params.window,
            params.number_of_points,
        );
        end_timer!(t0);

        Self::Config {
            stack,
            range_gate,
            vertical_gate,
            vanilla_gate,
            rom_gate,
        }
    }

    fn configure(_meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
        unreachable!();
    }

    fn without_witnesses(&self) -> Self {
        Self {
            params: self.params.clone(),
        }
    }

    fn synthesize(&self, mut cfg: Self::Config, ly: impl Layouter<C::Scalar>) -> Result<(), Error> {
        let ly_ctx = &mut LayoutCtx::new(ly);

        let t0 = start_timer!(|| "layout");

        cfg.stack.layout_range_limbs(ly_ctx, &cfg.vertical_gate)?;
        cfg.stack.layout_range_single(ly_ctx, &cfg.vertical_gate)?;
        cfg.stack.layout_range_tables(ly_ctx, &cfg.range_gate)?;
        cfg.stack.layout_first_degree(ly_ctx, &cfg.vanilla_gate)?;
        cfg.stack.layout_second_degree(ly_ctx, &cfg.vanilla_gate)?;
        cfg.stack.layout_rom(ly_ctx, &cfg.rom_gate)?;
        cfg.stack.apply_indirect_copy(ly_ctx)?;

        end_timer!(t0);

        Ok(())
    }

    fn params(&self) -> Self::Params {
        self.params.clone()
    }
}

fn run_test<
    C: CurveAffine,
    const RANGE_W: usize,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const SUBLIMB_SIZE: usize,
>(
    k: u32,
    number_of_points: usize,
    window: usize,
) where
    C::Scalar: FromUniformBytes<64>,
{
    let witness_aux = Value::known(C::Curve::random(OsRng).into());
    let constant_aux = C::Curve::random(OsRng).into();

    let params = Params {
        witness_aux,
        constant_aux,
        number_of_points,
        window,
    };
    let circuit = TestCircuit::<C, RANGE_W, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE> { params };
    let public_inputs = vec![];
    let prover = match MockProver::run(k, &circuit, public_inputs) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#}"),
    };
    prover.assert_satisfied();
}

#[test]
fn test_base_field_ecc() {
    use halo2::halo2curves::bn256::G1Affine;

    run_test::<
        G1Affine,
        2,
        3,  // number of limbs
        90, // limb size
        18, // sublimb size
    >(19, 100, 6);
}

#[test]
#[ignore]
fn bench_prover() {
    let witness_aux = Value::known(G1::random(OsRng).into());
    let constant_aux = G1::random(OsRng).into();

    let params = Params {
        witness_aux,
        constant_aux,
        number_of_points: 100,
        window: 6,
    };
    let circuit = TestCircuit::<G1Affine, 2, 3, 90, 18> { params };
    run_test_prover(19, circuit);
}
