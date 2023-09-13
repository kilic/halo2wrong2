use std::fmt::Debug;
use std::marker::PhantomData;
use std::path;

use ark_std::{end_timer, start_timer};

use circuitry::gates::range::in_place::RangeInPlaceGate;
use circuitry::gates::range::RangeInPlace;
use circuitry::gates::select::SelectGate;
use circuitry::gates::vanilla::VanillaGate;
use circuitry::gates::var_vanilla::VarVanillaGate;
use circuitry::gates::vertical::VerticalGate;
use circuitry::stack::Stack;
use ff::Field;
use ff::{FromUniformBytes, PrimeField};
use group::{Curve, Group};

use halo2::halo2curves::bn256::{Bn256, Fq, Fr, G1Affine, G1};
use halo2::halo2curves::pairing::Engine;
use halo2::halo2curves::pasta::Fp;
use halo2::plonk::{create_proof, keygen_pk, keygen_vk, ProvingKey};
use halo2::poly::commitment::{Params, ParamsProver};
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
use crate::utils::_multiexp_naive_var;
use crate::Point;

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
) -> Stack<C::Scalar> {
    let stack = &mut Stack::<C::Scalar>::default();

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

    let points: Vec<C::CurveExt> = (0..number_of_points)
        .map(|_| C::CurveExt::random(OsRng))
        .collect();
    let scalars: Vec<C::Scalar> = (0..number_of_points)
        .map(|_| C::Scalar::random(OsRng))
        .collect();

    let res0 = _multiexp_naive_var(&points[..], &scalars[..]);

    let res0 = ch.assign_point(stack, value(res0.into()));
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

    let res1 = ch.msm_sliding_vertical(stack, &points[..], &scalars[..], window_size);
    // ch.normal_equal(stack, &res0, &res1);

    // let res2 = ch.msm_sliding_horizontal(stack, &points[..], &scalars[..], window_size);
    // println!("res0 {:?}", res0.value::<C>());
    // println!("res1 {:?}", res1.value::<C>());
    // println!("res2 {:?}", res2.value::<C>());
    // ch.normal_equal(stack, &res0, &res1);

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
    select_gate: SelectGate<C::Scalar>,
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

        let select_gate = SelectGate::new(
            meta,
            shared_columns[0],
            shared_columns[1],
            shared_columns[2],
            shared_columns[3],
        );
        select_gate.configure(meta);

        Self::Config {
            rns,
            vertical_gate,
            vanilla_gate,
            select_gate,
        }
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

        stack.layout_selections(ly_ctx, &cfg.select_gate)?;

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
    C::Scalar: FromUniformBytes<64>,
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
fn test_ecc_x() {
    use halo2::halo2curves::pasta::{Eq, EqAffine};

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
    >(21, 100, 4);

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
)
// where
// E::Scalar: FromUniformBytes<64>,
{
    // use halo2::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
    // use halo2::poly::kzg::multiopen::{ProverGWC, VerifierGWC};
    // use halo2::poly::kzg::strategy::AccumulatorStrategy;

    // use halo2curves::bn256::Bn256;

    // let params = create_srs(k);
    // // println!("XXX\n{:#?}", params);
    // println!("params read");

    // println!("params write");
    // let params = write_srs(k);
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
    // let circuit = TestCircuit::<G1Affine, RangeInPlaceGate<Fr, 2>, 3, 88, 4, 22> {
    //     aux_generator,
    //     _marker: PhantomData,
    // };

    // run_test_prover::<
    //     _,
    //     3,  // number of limbs
    //     88, // limb size
    //     4,  // number of sublimbs
    //     22, // sublimb size
    // >(23, circuit);

    // let circuit = TestCircuit::<G1Affine, RangeInPlaceSpaseGate<Fr, 2, 22>, 3, 88, 4, 22> {
    //     aux_generator,
    //     _marker: PhantomData,
    // };

    // run_test_prover::<
    //     _,
    //     3,  // number of limbs
    //     88, // limb size
    //     4,  // number of sublimbs
    //     22, // sublimb size
    // >(23, circuit);

    // let circuit = TestCircuit::<G1Affine, RangeInPlaceSpaseGate<Fr, 2, 18>, 3, 90, 5, 18> {
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
    >(21, circuit);
}

fn write_srs(k: u32) -> ParamsKZG<Bn256> {
    let path = format!("srs_{k}.bin");
    let params = ParamsKZG::<Bn256>::new(k);
    params
        .write_custom(
            &mut std::fs::File::create(path).unwrap(),
            halo2::SerdeFormat::RawBytesUnchecked,
        )
        .unwrap();
    params
}

fn read_srs(k: u32) -> ParamsKZG<Bn256> {
    let path = format!("srs_{k}.bin");
    let file = std::fs::File::open(path.as_str());
    match file {
        Ok(mut file) => {
            ParamsKZG::<Bn256>::read_custom(&mut file, halo2::SerdeFormat::RawBytesUnchecked)
                .unwrap()
        }
        Err(_) => write_srs(k),
    }
}

// fn write_keygen<
//     const NUMBER_OF_LIMBS: usize,
//     const LIMB_SIZE: usize,
//     const NUMBER_OF_SUBLIMBS: usize,
//     const SUBLIMB_SIZE: usize,
// >(
//     params: ParamsKZG<Bn256>,
//     circuit: TestCircuit<G1Affine, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>,
// ) -> ProvingKey<G1Affine> {
//     println!("gen vk");
//     let vk = keygen_vk(&params, &circuit).unwrap();
//     println!("gen pk");
//     let pk = keygen_pk(&params, vk, &circuit).unwrap();
//     println!("pk write");
//     pk.write(
//         &mut std::fs::File::create("pk.bin").unwrap(),
//         halo2::SerdeFormat::RawBytesUnchecked,
//     )
//     .unwrap();
//     println!("pk ret");
//     pk
// }

// fn read_keygen<
//     const NUMBER_OF_LIMBS: usize,
//     const LIMB_SIZE: usize,
//     const NUMBER_OF_SUBLIMBS: usize,
//     const SUBLIMB_SIZE: usize,
// >() -> ProvingKey<G1Affine> {
//     ProvingKey::read::<
//         _,
//         TestCircuit<G1Affine, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>,
//     >(
//         &mut std::fs::File::create("pk.bin").unwrap(),
//         halo2::SerdeFormat::RawBytesUnchecked,
//         (),
//     )
//     .unwrap()
// }

// impl<
//         C: CurveAffine,
//         LA,
//         LR,
//         const NUMBER_OF_LIMBS: usize,
//         const LIMB_SIZE: usize,
//         const NUMBER_OF_SUBLIMBS: usize,
//         const SUBLIMB_SIZE: usize,
//     > Circuit<C::Scalar>
//     for TestCircuit<C, LA, LR, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>
// where
//     LA: GateLayout<C::Scalar, Enforcement = ArithmeticEnforcement<C::Scalar>, Params = ()>,
//     LR: GateLayout<C::Scalar, Enforcement = RangeEnforcement<C::Scalar>, Params = ()>,
// {
//     type Config =
//         TestConfig<C, LA, LR, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>;
//     type FloorPlanner = SimpleFloorPlanner;

//     type Params = ();

//     fn configure(_: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
//         unreachable!();
//     }

//     fn without_witnesses(&self) -> Self {
//         Self {
//             _marker: PhantomData,
//         }
//     }

//     fn configure_with_params(
//         meta: &mut ConstraintSystem<C::Scalar>,
//         _params: Self::Params,
//     ) -> Self::Config {
//         let rns = Rns::construct();
//         Self::Config {
//             rns,
//             arithmetic_layouter: LA::configure(meta, ()),
//             range_layouter: LR::configure(meta, ()),
//         }
//     }

//     fn synthesize(
//         &self,
//         config: Self::Config,
//         mut ly: impl Layouter<C::Scalar>,
//     ) -> Result<(), Error> {
//         let aux = C::CurveExt::random(OsRng).to_affine();
//         // let ch = BaseFieldEccChip::<C,_,_,_,_,>::new(&config.rns, aux);
//         Ok(())
//     }
// }

// println!("write keygen");
// let pk0 = write_keygen(params, circuit);

// println!("read keygen");
// let pk1: ProvingKey<G1Affine> =
//     read_keygen::<NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>();

// println!("end");

// let _ = pk1.get_vk();

// let vk = keygen_vk(&params, &circuit).unwrap();
// println!("pk");
// let pk = keygen_pk(&params, vk, &circuit).unwrap();

// println!("keygen end");

// println!("YYY\n{:#?}", params);

// let params = ParamsKZG::<Bn256>::new(k);
// params.write(writer)
// params.write(writer);
// println!("vk");
// let vk = keygen_vk(&params, &circuit).unwrap();
// println!("pk");
// let pk = keygen_pk(&params, vk, &circuit).unwrap();
// println!("keygen end");

// let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
// // let t0 = start_timer!(|| "prover");

// let proof = create_proof::<KZGCommitmentScheme<Bn256>, ProverSHPLONK<Bn256>, _, _, _, _>(
//     &params,
//     &pk,
//     &[circuit],
//     &[&[]],
//     OsRng,
//     &mut transcript,
// );

// //     transcript.finalize()
// // };
// end_timer!(t0);

// proof.expect("proof generation should not fail");

// let accepted = {
//     let strategy = AccumulatorStrategy::new(&params);
//     let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);

//     verify_proof::<IPACommitmentScheme<C>, VerifierIPA<C>, _, _, _>(
//         &params,
//         pk.get_vk(),
//         strategy,
//         &[&[]],
//         &mut transcript,
//     )
//     .map(|strategy| strategy.finalize())
//     .unwrap_or_default()
// };

// assert_eq!(accepted, expected);

struct State {
    x1: Fq,
    y1: Fq,
    x3: Fq,
    lambda: Fq,
}

fn chain_start(p1: (Fq, Fq), p2: (Fq, Fq)) -> State {
    let (x1, y1) = p1;
    let (x2, y2) = p2;

    let lambda = (y2 - y1) * (x2 - x1).invert().unwrap();
    let x3 = lambda * lambda - (x2 + x1);
    State { x1, y1, x3, lambda }
}

fn chain_add(state: &mut State, e: (Fq, Fq)) {
    let (p1x, p1y) = e;

    let lambda = state.lambda * (state.x3 - state.x1) + state.y1 + p1y;
    let lambda = lambda * (p1x - state.x3).invert().unwrap();

    let x3 = lambda * lambda - state.x3 - p1x;

    state.x1 = p1x;
    state.y1 = p1y;
    state.lambda = lambda;
    state.x3 = x3;
}

fn chain_end(state: State) -> G1Affine {
    let State { x1, y1, x3, lambda } = state;
    let y3 = lambda * (x1 - x3) - y1;
    println!("x {:?}", x3);
    println!("y {:?}", y3);
    G1Affine::from_xy(x3, y3).unwrap()
}

#[test]
fn test_lambda_trick() {
    let n = 102;
    let points = (0..n).map(|_| G1Affine::random(OsRng)).collect::<Vec<_>>();

    let expect = points.iter().fold(G1::identity(), |acc, p| acc + p);
    let expect = expect.to_affine();

    let points = points
        .iter()
        .map(|p| {
            let coords = p.coordinates().unwrap();
            (coords.x().clone(), coords.y().clone())
        })
        .collect::<Vec<_>>();

    let a0 = points[0];
    let a1 = points[1];
    let mut state = chain_start(a0, a1);

    // chain_add(&mut state, points[2]);

    for points in points.iter().skip(2) {
        chain_add(&mut state, *points);
    }
    let result = chain_end(state);

    println!("expect: {:#?}", expect);

    println!("result: {:#?}", result);
}

// template <typename C, class Fq, class Fr, class G>
// typename element<C, Fq, Fr, G>::chain_add_accumulator element<C, Fq, Fr, G>::chain_add_start(const element& p1,
//                                                                                              const element& p2)
// {
//     chain_add_accumulator output;
//     output.x1_prev = p1.x;
//     output.y1_prev = p1.y;

//     p1.x.assert_is_not_equal(p2.x);
//     const Fq lambda = Fq::div_without_denominator_check({ p2.y, -p1.y }, (p2.x - p1.x));

//     const Fq x3 = lambda.sqradd({ -p2.x, -p1.x });
//     output.x3_prev = x3;
//     output.lambda_prev = lambda;
//     return output;
// }

// * number of compositions: 259970
// * * zerosum n: 4 occurs: 47456
// * * zerosum n: 6 occurs: 141848
// * * zerosum n: 7 occurs: 70566
// * * zerosum n: 256 occurs: 100
// * * rows: 1560475

// layout second degree composition
// * * zerosum n: 2 nn: 1 occurs: 8400
// * * zerosum n: 3 nn: 1 occurs: 23522
// * * zerosum n: 4 nn: 1 occurs: 15122
// * * zerosum n: 5 nn: 1 occurs: 737
// * * zerosum n: 5 nn: 2 occurs: 7663
// * * zerosum n: 6 nn: 1 occurs: 7561
// * * zerosum n: 6 nn: 2 occurs: 8298
// * * zerosum n: 6 nn: 3 occurs: 7663
// * * zerosum n: 7 nn: 2 occurs: 7561
// * * zerosum n: 7 nn: 3 occurs: 7561
// * * rows: 342957

// layout simple composition
// ---
// * number of compositions: 182492
// * * zerosum n: 2 occurs: 67392
// * * zerosum n: 3 occurs: 115100
// * * rows: 182493

// layout selections
// ---
// * number of selects: 765000
// * * rows: 1530001

// layout range tables
// ---
// * in place range table: [1, 2, 3, 17, 18]
