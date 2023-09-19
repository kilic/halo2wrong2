use std::marker::PhantomData;

use ark_std::{end_timer, start_timer};

use circuitry::gates::range::in_place::RangeInPlaceGate;
use circuitry::gates::range::RangeInPlace;
use circuitry::gates::rom::ROMGate;
use circuitry::gates::var_vanilla::VarVanillaGate;
use circuitry::gates::vertical::VerticalGate;
use circuitry::stack::Stack;
use ff::Field;
use ff::PrimeField;
use group::{Curve, Group};

use halo2::halo2curves::bn256::{Bn256, Fr, G1Affine, G1};
use halo2::halo2curves::pasta::Fp;
use halo2::halo2curves::CurveExt;
use halo2::halo2curves::FieldExt;
use halo2::plonk::{create_proof, keygen_pk, keygen_vk, Advice, Column};
use halo2::poly::commitment::ParamsProver;
use halo2::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2::poly::kzg::multiopen::ProverSHPLONK;
use halo2::transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer};
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
use crate::Point;

pub(crate) fn _multiexp_naive_var<C: CurveExt>(point: &[C], scalar: &[C::ScalarExt]) -> C
where
    <C::ScalarExt as PrimeField>::Repr: AsRef<[u8]>,
{
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
    const NUMBER_OF_SUBLIMBS: usize,
    const SUBLIMB_SIZE: usize,
>(
    rns: &Rns<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
    aux_generator: Value<C>,
    window_size: usize,
    number_of_points: usize,
) -> Stack<C::Scalar, NUMBER_OF_LIMBS> {
    let stack = &mut Stack::<C::Scalar, NUMBER_OF_LIMBS>::default();

    let ch: BaseFieldEccChip<C, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE> =
        BaseFieldEccChip::new(rns, aux_generator);

    fn value<T>(e: T) -> Value<T> {
        Value::known(e)
    }

    // constant registry
    // {
    //     let p = C::CurveExt::random(OsRng);
    //     let p_val = Value::known(p.into());
    //     let p_assigned = ch.assign_point(stack, p_val);
    //     let p_constant = ch.register_constant(stack, p.into());
    //     ch.assert_on_curve(stack, &p_constant);
    //     ch.copy_equal(stack, &p_assigned, &p_constant);
    //     ch.normal_equal(stack, &p_assigned, &p_constant);
    // }

    // // add
    // {
    //     let a: Value<C> = value(C::CurveExt::random(OsRng).into());
    //     let b: Value<C> = value(C::CurveExt::random(OsRng).into());
    //     let c: Value<C> = (a + b).map(|p| p.to_affine());
    //     let a = ch.assign_point(stack, a);
    //     let b = ch.assign_point(stack, b);
    //     let c0 = ch.assign_point(stack, c);
    //     let c1 = ch.add_incomplete(stack, &a, &b);
    //     ch.normal_equal(stack, &c0, &c1);

    //     let a: Value<C> = value(C::CurveExt::random(OsRng).into());
    //     let b: Value<C> = value(C::CurveExt::random(OsRng).into());
    //     let c: Value<C> = (a - b).map(|p| p.to_affine());
    //     let a = ch.assign_point(stack, a);
    //     let b = ch.assign_point(stack, b);
    //     let c0 = ch.assign_point(stack, c);
    //     let c1 = ch.sub_incomplete(stack, &a, &b);
    //     ch.normal_equal(stack, &c0, &c1);

    //     let n = 10;
    //     let points: Vec<C::CurveExt> = (0..n).map(|_| C::CurveExt::random(OsRng)).collect();
    //     let sum = points
    //         .iter()
    //         .fold(C::CurveExt::identity(), |acc, p| acc + p);
    //     let u0 = ch.assign_point(stack, value(sum.into()));
    //     let points = points
    //         .into_iter()
    //         .map(|p| ch.assign_point(stack, value(p.to_affine())))
    //         .collect::<Vec<_>>();
    //     let u1 = ch.add_multi(stack, &points[..]);
    //     println!("u0 {:?}", u0.value::<C>());
    //     println!("u1 {:?}", u1.value::<C>());
    //     ch.normal_equal(stack, &u0, &u1);
    // }

    // // double
    // {
    //     let a: Value<C> = value(C::CurveExt::random(OsRng).into());
    //     let c = (a + a).map(|p| p.to_affine());
    //     let a = ch.assign_point(stack, a);
    //     let c0 = ch.assign_point(stack, c);
    //     let c1 = ch.double_incomplete(stack, &a);
    //     ch.normal_equal(stack, &c0, &c1);
    // }

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
        .zip(scalars.into_iter())
        .map(|(point, scalar)| {
            let point = ch.assign_point(stack, value(point.into()));
            let scalar = ch.assign_scalar(stack, value(scalar));
            (point, scalar)
        })
        .unzip();

    let res1 = ch.msm_sliding_vertical_rom(stack, tag0, &points[..], &scalars[..], window_size);
    res1.value::<C>().map(|res1| assert_eq!(res0, res1));

    let res0 = ch.assign_point(stack, value(res0.into()));
    ch.normal_equal(stack, &res0, &res1);

    stack.clone()
}

#[derive(Clone)]
struct TestConfig<
    C: CurveAffine,
    R: RangeInPlace<C::Scalar, 1>,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const NUMBER_OF_SUBLIMBS: usize,
    const SUBLIMB_SIZE: usize,
> {
    vertical_gate: VerticalGate<C::Scalar, R>,
    vanilla_gate: VarVanillaGate<C::Scalar, 4>,
    // select_gate: SelectGate<C::Scalar>,
    rom_gate: ROMGate<C::Scalar, NUMBER_OF_LIMBS>,
    rns: Rns<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
}

#[derive(Default)]
struct TestCircuit<
    C: CurveAffine,
    R: RangeInPlace<C::Scalar, 1>,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const NUMBER_OF_SUBLIMBS: usize,
    const SUBLIMB_SIZE: usize,
> {
    aux_generator: Value<C>,
    number_of_points: usize,
    window: usize,
    _marker: PhantomData<R>,
}

impl<
        C: CurveAffine,
        R: RangeInPlace<C::Scalar, 1>,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const NUMBER_OF_SUBLIMBS: usize,
        const SUBLIMB_SIZE: usize,
    > Circuit<C::Scalar>
    for TestCircuit<C, R, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>
{
    type Config = TestConfig<C, R, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>;
    type FloorPlanner = SimpleFloorPlanner;

    fn configure(meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
        let rns = Rns::construct();

        let advice = meta.advice_column();
        let range_gate = R::configure(meta, [advice]);

        let acc = meta.advice_column();
        let scale = meta.fixed_column();

        let mut vertical_gate = VerticalGate::new(meta, range_gate, scale, advice, acc);
        vertical_gate.configure_composition_gate(meta);

        let vanilla_gate = VarVanillaGate::new(meta);
        vanilla_gate.configure(meta);
        let shared_columns = vanilla_gate.advice_colums();
        let rom_value_columns: [Column<Advice>; NUMBER_OF_LIMBS] =
            shared_columns[0..NUMBER_OF_LIMBS].try_into().unwrap();
        let query_fraction = shared_columns.last().unwrap();

        let rom_gate = ROMGate::configure(
            meta,
            *query_fraction,
            rom_value_columns.clone(),
            rom_value_columns.clone(),
        );

        // let select_gate = SelectGate::new(
        //     meta,
        //     shared_columns[0],
        //     shared_columns[1],
        //     shared_columns[2],
        //     shared_columns[3],
        // );
        // select_gate.configure(meta);

        Self::Config {
            rns,
            vertical_gate,
            vanilla_gate,
            rom_gate,
        }
        // select_gate,
    }

    fn without_witnesses(&self) -> Self {
        Self {
            aux_generator: Value::unknown(),
            number_of_points: self.number_of_points,
            window: self.window,
            _marker: PhantomData,
        }
    }

    fn synthesize(&self, cfg: Self::Config, ly: impl Layouter<C::Scalar>) -> Result<(), Error> {
        // let t0 = start_timer!(|| "stack");
        // println!("synth");

        let mut stack = make_stack::<C, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>(
            &cfg.rns,
            self.aux_generator,
            self.window,
            self.number_of_points,
        );

        let ly_ctx = &mut LayoutCtx::new(ly);

        stack.layout_range_compositions(ly_ctx, &cfg.vertical_gate)?;
        stack.layout_range_tables(ly_ctx, &cfg.vertical_gate)?;

        stack.layout_first_degree_compositions(ly_ctx, &cfg.vanilla_gate)?;
        stack.layout_first_degree_ternary_compositions(ly_ctx, &cfg.vanilla_gate)?;
        stack.layout_second_degree_compositions(ly_ctx, &cfg.vanilla_gate)?;

        stack.layout_rom(ly_ctx, &cfg.rom_gate)?;

        // stack.layout_selections(ly_ctx, &cfg.select_gate)?;

        stack.apply_indirect_copies(ly_ctx)?;

        Ok(())
    }
}

fn run_test<
    C: CurveAffine,
    R: RangeInPlace<C::Scalar, 1>,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const NUMBER_OF_SUBLIMBS: usize,
    const SUBLIMB_SIZE: usize,
>(
    k: u32,
    number_of_points: usize,
    window: usize,
) where
    C::Scalar: FieldExt,
{
    // let aux_generator = Value::known(C::CurveExt::random(OsRng).into());
    let aux_generator = Value::known(C::CurveExt::generator().into());
    let circuit = TestCircuit::<C, R, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE> {
        aux_generator,
        number_of_points,
        window,
        _marker: PhantomData,
    };
    // let public_inputs = vec![vec![]];
    let public_inputs = vec![];
    let prover = match MockProver::run(k, &circuit, public_inputs) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#}"),
    };
    prover.assert_satisfied();
}

#[test]
fn test_msm() {
    use halo2::halo2curves::pasta::EqAffine;

    // run_test::<
    //     EqAffine,
    //     3,  // number of limbs
    //     88, // limb size
    //     4,  // number of sublimbs
    //     22, // sublimb size
    // >(23);

    run_test::<
        EqAffine,
        RangeInPlaceGate<Fp, 1>,
        3,  // number of limbs
        90, // limb size
        5,  // number of sublimbs
        18, // sublimb size
    >(20, 100, 6);

    // run_test::<
    //     EqAffine,
    //     RangeInPlaceSpaseGate<Fp, 2, 18>,
    //     3,  // number of limbs
    //     90, // limb size
    //     5,  // number of sublimbs
    //     18, // sublimb size
    // >(20);
}

fn run_test_prover<
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const NUMBER_OF_SUBLIMBS: usize,
    const SUBLIMB_SIZE: usize,
>(
    k: u32,
    circuit: TestCircuit<
        G1Affine,
        RangeInPlaceGate<Fr, 1>,
        NUMBER_OF_LIMBS,
        LIMB_SIZE,
        NUMBER_OF_SUBLIMBS,
        SUBLIMB_SIZE,
    >,
) {
    println!("params read");
    let params = read_srs(k);
    println!("gen vk");
    let vk = keygen_vk(&params, &circuit).unwrap();
    println!("gen pk");
    let pk = keygen_pk(&params, vk, &circuit).unwrap();
    println!("pk write");

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    let t0 = start_timer!(|| "prover");
    let proof = create_proof::<KZGCommitmentScheme<Bn256>, ProverSHPLONK<Bn256>, _, _, _, _>(
        &params,
        &pk,
        &[circuit],
        &[&[]],
        OsRng,
        &mut transcript,
    );
    end_timer!(t0);

    proof.expect("proof generation should not fail");
}

#[test]
fn test_prover() {
    let aux_generator = Value::known(G1::random(OsRng).into());

    let circuit = TestCircuit::<G1Affine, RangeInPlaceGate<Fr, 1>, 3, 90, 5, 18> {
        aux_generator,
        number_of_points: 100,
        window: 4,
        _marker: PhantomData,
    };

    run_test_prover::<
        3,  // number of limbs
        90, // limb size
        5,  // number of sublimbs
        18, // sublimb size
    >(20, circuit);
}

fn write_srs(k: u32) -> ParamsKZG<Bn256> {
    let path = format!("srs_{k}.bin");
    let params = ParamsKZG::<Bn256>::new(k);
    params.write_custom(
        &mut std::fs::File::create(path).unwrap(),
        halo2::SerdeFormat::RawBytesUnchecked,
    );

    params
}

fn read_srs(k: u32) -> ParamsKZG<Bn256> {
    let path = format!("srs_{k}.bin");
    let file = std::fs::File::open(path.as_str());
    match file {
        Ok(mut file) => {
            ParamsKZG::<Bn256>::read_custom(&mut file, halo2::SerdeFormat::RawBytesUnchecked)
        }
        Err(_) => write_srs(k),
    }
}
