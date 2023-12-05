use circuitry::{chip::first_degree::FirstDegreeChip, stack::Stack, witness::Witness};
use ecc::Point;
use halo2::{arithmetic::CurveAffine, halo2curves::ff::PrimeField, plonk::Error};
use integer::chip::IntegerChip;
use poseidon::Spec;

use crate::PoseidonChip;

/// `PointRepresentation` will encode point with an implemented strategy
pub trait PointRepresentation<C: CurveAffine, N: PrimeField + Ord>: Default {
    fn encode_assigned<
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    >(
        stack: &mut Stack<N>,
        integer_chip: IntegerChip<C::Base, N, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>,
        point: &Point<C::Base, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Vec<Witness<N>>;
}

/// `LimbRepresentation` encodes point as `[[limbs_of(x)],  sign_of(y)]`
#[derive(Default)]
pub struct LimbRepresentation;

impl<C: CurveAffine, N: PrimeField + Ord> PointRepresentation<C, N> for LimbRepresentation {
    fn encode_assigned<
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    >(
        stack: &mut Stack<N>,
        integer_chip: IntegerChip<C::Base, N, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>,
        point: &Point<C::Base, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Vec<Witness<N>> {
        let mut encoded: Vec<Witness<N>> = point.x().limbs().to_vec();
        let sign = integer_chip.sign(stack, point.y());
        encoded.push(sign);
        encoded
    }
}

/// `NativeRepresentation` encodes point as `[native(x),  native(y)]`
#[derive(Default)]
pub struct NativeRepresentation;

impl<C: CurveAffine, N: PrimeField + Ord> PointRepresentation<C, N> for NativeRepresentation {
    fn encode_assigned<
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    >(
        _stack: &mut Stack<N>,
        _integer_chip: IntegerChip<C::Base, N, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>,
        point: &Point<C::Base, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Vec<Witness<N>> {
        vec![*point.x().native(), *point.y().native()]
    }
}

#[derive(Clone, Debug)]
pub struct TranscriptChip<N: PrimeField + Ord, const T: usize, const RATE: usize> {
    poseidon: PoseidonChip<N, T, RATE>,
}

impl<N: PrimeField + Ord, const T: usize, const RATE: usize> TranscriptChip<N, T, RATE> {
    /// Constructs the transcript chip
    pub fn new(stack: &mut impl FirstDegreeChip<N>, spec: &Spec<N, T, RATE>) -> Self {
        let poseidon = PoseidonChip::new(stack, spec);
        Self { poseidon }
    }

    /// Write scalar to the transcript
    pub fn write_scalar(&mut self, scalar: &Witness<N>) {
        self.poseidon.update(&[*scalar]);
    }

    /// Write point to the transcript
    pub fn write_point<
        C: CurveAffine,
        E: PointRepresentation<C, N>,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    >(
        &mut self,
        stack: &mut Stack<N>,
        integer_chip: IntegerChip<C::Base, N, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>,
        point: &Point<C::Base, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Result<(), Error> {
        let encoded = E::encode_assigned(stack, integer_chip, point);
        self.poseidon.update(&encoded[..]);
        Ok(())
    }

    // Constrain squeezing new challenge
    pub fn squeeze(&mut self, stack: &mut Stack<N>) -> Witness<N> {
        self.poseidon.hash(stack)
    }
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use crate::TranscriptChip;
    use circuitry::chip::Core;
    use circuitry::gates::range::RangeGate;
    use circuitry::gates::vanilla::VanillaGate;
    use circuitry::gates::vertical::VerticalGate;
    use circuitry::stack::Stack;
    use circuitry::LayoutCtx;
    use halo2::circuit::Layouter;
    use halo2::circuit::SimpleFloorPlanner;
    use halo2::circuit::Value;
    use halo2::dev::MockProver;
    use halo2::halo2curves::ff::Field;
    use halo2::halo2curves::ff::FromUniformBytes;
    use halo2::halo2curves::CurveAffine;
    use halo2::plonk::Error;
    use halo2::plonk::{Circuit, ConstraintSystem};
    use paste::paste;
    use poseidon::Poseidon;
    use poseidon::Spec;
    use rand_core::OsRng;

    fn make_stack<
        C: CurveAffine,
        const T: usize,
        const RATE: usize,
        const RF: usize,
        const RP: usize,
    >() -> Stack<C::Scalar>
    where
        C::Scalar: FromUniformBytes<64>,
    {
        let stack = &mut Stack::<_>::default();

        let spec = Spec::<C::Scalar, T, RATE>::new(RF, RP);

        for number_of_inputs in 0..=3 * T + 1 {
            let mut ref_hasher = Poseidon::<C::Scalar, T, RATE>::new(RF, RP);
            let inputs = (0..number_of_inputs)
                .map(|_| C::Scalar::random(OsRng))
                .collect::<Vec<_>>();

            ref_hasher.update(&inputs[..]);
            let expected = ref_hasher.squeeze();
            let expected = stack.assign(Value::known(expected));

            let mut transcript = TranscriptChip::<_, T, RATE>::new(stack, &spec);

            let inputs = inputs
                .iter()
                .map(|e| stack.assign(Value::known(*e)))
                .collect::<Vec<_>>();

            for input in inputs.iter() {
                transcript.write_scalar(input);
            }
            let result = transcript.squeeze(stack);
            stack.equal(&result, &expected);
        }

        stack.clone()
    }

    #[derive(Clone)]
    struct TestConfig<
        C: CurveAffine,
        const T: usize,
        const RATE: usize,
        const RF: usize,
        const RP: usize,
    > {
        vertical_gate: VerticalGate<1>,
        vanilla_gate: VanillaGate,
        range_gate: RangeGate,
        stack: Stack<C::Scalar>,
    }

    struct TestCircuit<
        C: CurveAffine,
        const T: usize,
        const RATE: usize,
        const RF: usize,
        const RP: usize,
    >(PhantomData<C>);

    impl<C: CurveAffine, const T: usize, const RATE: usize, const RF: usize, const RP: usize>
        Circuit<C::Scalar> for TestCircuit<C, T, RATE, RF, RP>
    where
        C::Scalar: FromUniformBytes<64>,
    {
        type Config = TestConfig<C, T, RATE, RF, RP>;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn configure_with_params(
            meta: &mut ConstraintSystem<C::Scalar>,
            _params: Self::Params,
        ) -> Self::Config {
            let advices = (0..1).map(|_| meta.advice_column()).collect::<Vec<_>>();
            let range_gate = RangeGate::configure(meta, &advices[..]);
            let vertical_gate =
                VerticalGate::configure(meta, &range_gate, advices.try_into().unwrap());
            let vanilla_gate = VanillaGate::configure(meta);
            let stack = make_stack::<C, T, RATE, RF, RP>();

            Self::Config {
                stack,
                range_gate,
                vertical_gate,
                vanilla_gate,
            }
        }

        fn configure(_meta: &mut ConstraintSystem<C::Scalar>) -> Self::Config {
            unreachable!();
        }

        fn without_witnesses(&self) -> Self {
            Self(PhantomData)
        }

        fn synthesize(
            &self,
            mut cfg: Self::Config,
            ly: impl Layouter<C::Scalar>,
        ) -> Result<(), Error> {
            let ly_ctx = &mut LayoutCtx::new(ly);

            cfg.stack.layout_range_limbs(ly_ctx, &cfg.vertical_gate)?;
            cfg.stack.layout_range_single(ly_ctx, &cfg.vertical_gate)?;
            cfg.stack.layout_range_tables(ly_ctx, &cfg.range_gate)?;
            cfg.stack.layout_first_degree(ly_ctx, &cfg.vanilla_gate)?;
            cfg.stack.layout_second_degree(ly_ctx, &cfg.vanilla_gate)?;
            cfg.stack.apply_indirect_copy(ly_ctx)?;

            Ok(())
        }

        fn params(&self) -> Self::Params {}
    }

    macro_rules! test {
        ($RF:expr, $RP:expr, $T:expr, $RATE:expr) => {
            paste! {
                #[test]
                fn [<test_poseidon_ $RF _ $RP _ $T _ $RATE>]() {

                    use halo2::halo2curves::bn256::{G1Affine};

                        let circuit: TestCircuit<G1Affine, $T, $RATE, $RF, $RP> = TestCircuit(PhantomData);
                        let public_inputs = vec![];
                        let prover =
                            match MockProver::run(17, &circuit, public_inputs) {
                                Ok(prover) => prover,
                                Err(e) => panic!("{e:#}"),
                            };
                        prover.assert_satisfied();


                }
            }
        };
    }
    test!(8, 57, 3, 2);
    test!(8, 57, 4, 3);
    test!(8, 57, 5, 4);
    test!(8, 57, 6, 5);
    test!(8, 57, 7, 6);
    test!(8, 57, 8, 7);
    test!(8, 57, 9, 8);
    test!(8, 57, 10, 9);
}
