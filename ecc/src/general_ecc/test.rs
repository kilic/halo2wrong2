use crate::general_ecc::GeneralEccChip;
use crate::test::run_test_prover;
use crate::Point;
use ark_std::end_timer;
use ark_std::start_timer;
use circuitry::gates::range::RangeGate;
use circuitry::gates::rom::ROMGate;
use circuitry::gates::vanilla::VanillaGate;
use circuitry::gates::vertical::VerticalGate;
use circuitry::stack::Stack;
use circuitry::LayoutCtx;
use ff::Field;
use ff::FromUniformBytes;
use ff::PrimeField;
use group::{Curve, Group};
use halo2::halo2curves::bn256::Fr;
use halo2::halo2curves::pasta::Eq;
use halo2::halo2curves::pasta::EqAffine;
use halo2::halo2curves::CurveExt;
use halo2::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    halo2curves::CurveAffine,
    plonk::{Circuit, ConstraintSystem, Error},
};
use integer::integer::Integer;
use integer::rns::Rns;
use rand_core::OsRng;

pub(crate) fn _multiexp_naive_var<C: CurveExt>(point: &[C], scalar: &[C::Scalar]) -> C {
    assert!(!point.is_empty());
    assert_eq!(point.len(), scalar.len());
    point
        .iter()
        .zip(scalar.iter())
        .fold(C::identity(), |acc, (point, scalar)| {
            acc + (*point * *scalar)
        })
}

fn make_stack<Emulated: CurveAffine, N: PrimeField + Ord>(
    rns_base: &Rns<Emulated::Base, N>,
    rns_scalar: &Rns<Emulated::Scalar, N>,
    witness_aux: Value<Emulated>,
    constant_aux: Emulated,
    window_size: usize,
    number_of_points: usize,
    sublimb_size: usize,
) -> Stack<N> {
    let stack = &mut Stack::<N>::with_rom(rns_base.number_of_limbs);

    let ecc_ch: GeneralEccChip<Emulated, N> = GeneralEccChip::new(
        rns_base,
        rns_scalar,
        witness_aux,
        constant_aux,
        sublimb_size,
    );

    fn value<T>(e: T) -> Value<T> {
        Value::known(e)
    }

    // constant registry
    {
        let p = Emulated::Curve::random(OsRng);
        let p_val = Value::known(p.into());
        let p_assigned = ecc_ch.assign_point(stack, p_val);
        let p_constant = ecc_ch.register_constant(stack, p.into());
        ecc_ch.assert_on_curve(stack, &p_constant);
        ecc_ch.copy_equal(stack, &p_assigned, &p_constant);
        ecc_ch.normal_equal(stack, &p_assigned, &p_constant);
    }

    // add
    {
        let a: Value<Emulated> = value(Emulated::Curve::random(OsRng).into());
        let b: Value<Emulated> = value(Emulated::Curve::random(OsRng).into());
        let c: Value<Emulated> = (a + b).map(|p| p.to_affine());
        let a = ecc_ch.assign_point(stack, a);
        let b = ecc_ch.assign_point(stack, b);
        let c0 = ecc_ch.assign_point(stack, c);
        let c1 = ecc_ch.add_incomplete(stack, &a, &b);
        ecc_ch.normal_equal(stack, &c0, &c1);

        let a: Value<Emulated> = value(Emulated::Curve::random(OsRng).into());
        let b: Value<Emulated> = value(Emulated::Curve::random(OsRng).into());
        let c: Value<Emulated> = (a - b).map(|p| p.to_affine());
        let a = ecc_ch.assign_point(stack, a);
        let b = ecc_ch.assign_point(stack, b);
        let c0 = ecc_ch.assign_point(stack, c);
        let c1 = ecc_ch.sub_incomplete(stack, &a, &b);
        ecc_ch.normal_equal(stack, &c0, &c1);

        let n = 10;
        let points: Vec<Emulated::Curve> = (0..n).map(|_| Emulated::Curve::random(OsRng)).collect();
        let sum = points
            .iter()
            .fold(Emulated::Curve::identity(), |acc, p| acc + p);
        let u0 = ecc_ch.assign_point(stack, value(sum.into()));
        let points = points
            .into_iter()
            .map(|p| ecc_ch.assign_point(stack, value(p.to_affine())))
            .collect::<Vec<_>>();
        let u1 = ecc_ch.add_multi(stack, &points[..]);
        ecc_ch.normal_equal(stack, &u0, &u1);
    }

    // double
    {
        let a: Value<Emulated> = value(Emulated::Curve::random(OsRng).into());
        let c = (a + a).map(|p| p.to_affine());
        let a = ecc_ch.assign_point(stack, a);
        let c0 = ecc_ch.assign_point(stack, c);
        let c1 = ecc_ch.double_incomplete(stack, &a);
        ecc_ch.normal_equal(stack, &c0, &c1);
    }

    // mul var
    {
        let points: Vec<Emulated::Curve> = (0..number_of_points)
            .map(|_| Emulated::Curve::random(OsRng))
            .collect();

        let scalars: Vec<Emulated::Scalar> = (0..number_of_points)
            .map(|_| Emulated::Scalar::random(OsRng))
            .collect();

        let res0 = _multiexp_naive_var(&points[..], &scalars[..]).to_affine();

        #[allow(clippy::type_complexity)]
        let (points, scalars): (
            Vec<Point<Emulated::Base, N>>,
            Vec<Integer<Emulated::Scalar, N>>,
        ) = points
            .into_iter()
            .zip(scalars)
            .map(|(point, scalar)| {
                let point = ecc_ch.assign_point(stack, value(point.into()));
                let scalar = ecc_ch.assign_scalar(stack, value(scalar));
                (point, scalar)
            })
            .unzip();

        let res1: Point<<Emulated as CurveAffine>::Base, N> = ecc_ch.msm_sliding_vertical_rom(
            stack,
            N::random(OsRng),
            &points[..],
            &scalars[..],
            window_size,
        );
        res1.value::<Emulated>().map(|res1| assert_eq!(res0, res1));

        let res0 = ecc_ch.assign_point(stack, value(res0));
        ecc_ch.normal_equal(stack, &res0, &res1);
    }

    // mul fix
    {
        let point = Emulated::Curve::random(OsRng);
        let prepared = ecc_ch.prepare_mul_fix(stack, point.into());

        let scalar = Emulated::Scalar::random(OsRng);
        let res0 = _multiexp_naive_var(&[point], &[scalar]).to_affine();
        // let scalar = ecc_ch.assign_scalar(stack, value(scalar));
        let scalar = ecc_ch.assign_scalar(stack, value(scalar));
        let res1 = ecc_ch.mul_fix(stack, &prepared, &scalar);
        res1.value::<Emulated>().map(|res1| assert_eq!(res0, res1));
        let res1 = ecc_ch.mul_fix(stack, &prepared, &scalar);
        let res0 = ecc_ch.assign_point(stack, value(res0));
        ecc_ch.normal_equal(stack, &res0, &res1);
    }

    stack.clone()
}

#[derive(Clone)]
struct TestConfig<Emulated: CurveAffine, N: PrimeField + Ord, const RANGE_W: usize> {
    vertical_gate: VerticalGate<RANGE_W>,
    vanilla_gate: VanillaGate,
    range_gate: RangeGate,
    rom_gate: ROMGate,
    stack: Stack<N>,
    _marker: std::marker::PhantomData<Emulated>,
}

#[derive(Default, Clone)]
struct Params<Emulated: CurveAffine> {
    witness_aux: Value<Emulated>,
    constant_aux: Emulated,
    number_of_points: usize,
    window: usize,
    limb_size: usize,
    sublimb_size: usize,
}

#[derive(Default)]
struct TestCircuit<Emulated: CurveAffine, N: PrimeField + Ord, const RANGE_W: usize> {
    params: Params<Emulated>,
    _marker: std::marker::PhantomData<N>,
}

impl<Emulated: CurveAffine, N: PrimeField + Ord, const RANGE_W: usize> Circuit<N>
    for TestCircuit<Emulated, N, RANGE_W>
{
    type Config = TestConfig<Emulated, N, RANGE_W>;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = Params<Emulated>;

    fn configure_with_params(meta: &mut ConstraintSystem<N>, params: Self::Params) -> Self::Config {
        let advices = (0..RANGE_W)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>();

        let range_gate = RangeGate::configure(meta, &advices[..]);
        let vertical_gate = VerticalGate::configure(meta, &range_gate, advices.try_into().unwrap());
        let vanilla_gate = VanillaGate::configure(meta);

        let rns_base = Rns::construct(params.limb_size);
        let rns_scalar = Rns::construct(params.limb_size);

        let shared_columns = vanilla_gate.advice_colums();
        let rom_value_columns = shared_columns[0..rns_base.number_of_limbs].to_vec();
        let query_fraction = vertical_gate.advice_columns()[0];

        let rom_gate = ROMGate::configure(
            meta,
            query_fraction,
            &rom_value_columns[..],
            &rom_value_columns[..],
        );

        let t0 = start_timer!(|| "witness gen");
        let stack = make_stack::<Emulated, N>(
            &rns_base,
            &rns_scalar,
            params.witness_aux,
            params.constant_aux,
            params.window,
            params.number_of_points,
            params.sublimb_size,
        );
        end_timer!(t0);

        Self::Config {
            stack,
            range_gate,
            vertical_gate,
            vanilla_gate,
            rom_gate,
            _marker: std::marker::PhantomData,
        }
    }

    fn configure(_meta: &mut ConstraintSystem<N>) -> Self::Config {
        unreachable!();
    }

    fn without_witnesses(&self) -> Self {
        Self {
            params: self.params.clone(),
            _marker: std::marker::PhantomData,
        }
    }

    fn synthesize(&self, mut cfg: Self::Config, ly: impl Layouter<N>) -> Result<(), Error> {
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

fn run_test<Emulated: CurveAffine, N: PrimeField + Ord, const RANGE_W: usize>(
    k: u32,
    limb_size: usize,
    sublimb_size: usize,
    number_of_points: usize,
    window: usize,
) where
    N: FromUniformBytes<64>,
{
    let witness_aux = Value::known(Emulated::Curve::random(OsRng).into());
    let constant_aux = Emulated::Curve::random(OsRng).into();
    let params = Params {
        witness_aux,
        constant_aux,
        number_of_points,
        window,
        limb_size,
        sublimb_size,
    };
    let circuit = TestCircuit::<Emulated, N, RANGE_W> {
        params,
        _marker: std::marker::PhantomData,
    };
    let public_inputs = vec![];
    let prover = match MockProver::run(k, &circuit, public_inputs) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#}"),
    };
    prover.assert_satisfied();
}

#[test]
fn test_general_ecc() {
    run_test::<EqAffine, Fr, 2>(19, 90, 18, 100, 6);
}

#[test]
#[ignore]
fn bench_prover() {
    let witness_aux = Value::known(Eq::random(OsRng).into());
    let constant_aux = Eq::random(OsRng).into();
    let params = Params {
        witness_aux,
        constant_aux,
        number_of_points: 100,
        window: 6,
        limb_size: 90,
        sublimb_size: 18,
    };

    let circuit = TestCircuit::<EqAffine, Fr, 2> {
        params,
        _marker: std::marker::PhantomData,
    };
    run_test_prover(19, circuit);
}
