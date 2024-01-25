use circuitry::stack::Stack;
use ff::PrimeField;
use halo2::halo2curves::CurveAffine;
use integer::integer::Integer;

use crate::Point;

use super::{mul_fix::FixMul, GeneralEccChip};

impl<
        Emulated: CurveAffine,
        N: PrimeField + Ord,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    > GeneralEccChip<Emulated, N, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>
{
    pub fn verify_ecdsa(
        &self,
        stack: &mut Stack<N>,
        prepared: &FixMul<Emulated, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        pub_key: &Point<Emulated::Base, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        message: &Integer<Emulated::Scalar, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        r: &Integer<Emulated::Scalar, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        s: &Integer<Emulated::Scalar, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        // 1. check 0 < r, s < n

        // since `assert_not_zero` already includes a in-field check, we can just
        // call `assert_not_zero`
        self.ch_scalar.assert_not_zero(stack, r);
        self.ch_scalar.assert_not_zero(stack, s);

        // 2. w = s^(-1) (mod n)
        // 3. u1 = m' * w (mod n)
        let u1 = self.ch_scalar.div(stack, message, s);

        // 4. u2 = r * w (mod n)
        let u2 = self.ch_scalar.div(stack, r, s);

        // 5. compute Q = u1*G + u2*pk
        let u1_g = self.mul_fix(stack, prepared, &u1);
        let u2_pk = self.msm_sliding_horizontal(stack, &[pub_key.clone()], &[u2], 4);
        let q = self.add_incomplete(stack, &u1_g, &u2_pk);

        // 6. reduce q_x in E::ScalarExt
        // assuming E::Base/E::ScalarExt have the same number of limbs
        let q_x = q.x();
        let q_x_reduced = self.ch_scalar.reduce_external(stack, q_x);
        self.ch_scalar.copy_equal(stack, &q_x_reduced, &r);
    }
}

#[cfg(test)]
mod test {

    use crate::general_ecc::GeneralEccChip;

    use ark_std::end_timer;
    use ark_std::start_timer;
    use circuitry::gates::range::RangeGate;
    use circuitry::gates::rom::ROMGate;
    use circuitry::gates::vanilla::VanillaGate;
    use circuitry::gates::vertical::VerticalGate;
    use circuitry::stack::Stack;
    use circuitry::utils::fe_to_fe;
    use circuitry::LayoutCtx;
    use ff::Field;
    use ff::FromUniformBytes;
    use ff::PrimeField;
    use group::{Curve, Group};
    use halo2::halo2curves::bn256::Fr;

    use halo2::halo2curves::pasta::EqAffine;
    use halo2::halo2curves::CurveExt;
    use halo2::plonk::{Advice, Column};
    use halo2::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        halo2curves::CurveAffine,
        plonk::{Circuit, ConstraintSystem, Error},
    };

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

    fn make_stack<
        Emulated: CurveAffine,
        N: PrimeField + Ord,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    >(
        rns_base: &Rns<Emulated::Base, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        rns_scalar: &Rns<Emulated::Scalar, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        witness_aux: Value<Emulated>,
        constant_aux: Emulated,
        pub_key: Value<Emulated>,
        message: Value<Emulated::Scalar>,
        r: Value<Emulated::Scalar>,
        s: Value<Emulated::Scalar>,
    ) -> Stack<N> {
        let stack = &mut Stack::<N>::with_rom(NUMBER_OF_LIMBS);

        let ecc_ch: GeneralEccChip<Emulated, N, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE> =
            GeneralEccChip::new(rns_base, rns_scalar, witness_aux, constant_aux);

        let g = Emulated::generator();
        let g_prepared = ecc_ch.prepare_mul_fix(stack, g.into());

        let message = ecc_ch.assign_scalar(stack, message);
        let pub_key = ecc_ch.assign_point(stack, pub_key);
        let r = ecc_ch.assign_scalar(stack, r);
        let s = ecc_ch.assign_scalar(stack, s);

        ecc_ch.verify_ecdsa(stack, &g_prepared, &pub_key, &message, &r, &s);

        stack.clone()
    }

    #[derive(Clone)]
    struct TestConfig<
        Emulated: CurveAffine,
        N: PrimeField + Ord,
        const RANGE_W: usize,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    > {
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
        pub_key: Value<Emulated>,
        message: Value<Emulated::Scalar>,
        r: Value<Emulated::Scalar>,
        s: Value<Emulated::Scalar>,
    }

    #[derive(Default)]
    struct TestCircuit<
        Emulated: CurveAffine,
        N: PrimeField + Ord,
        const RANGE_W: usize,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    > {
        params: Params<Emulated>,
        _marker: std::marker::PhantomData<N>,
    }

    impl<
            Emulated: CurveAffine,
            N: PrimeField + Ord,
            const RANGE_W: usize,
            const NUMBER_OF_LIMBS: usize,
            const LIMB_SIZE: usize,
            const SUBLIMB_SIZE: usize,
        > Circuit<N>
        for TestCircuit<Emulated, N, RANGE_W, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>
    {
        type Config = TestConfig<Emulated, N, RANGE_W, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>;
        type FloorPlanner = SimpleFloorPlanner;
        type Params = Params<Emulated>;

        fn configure_with_params(
            meta: &mut ConstraintSystem<N>,
            params: Self::Params,
        ) -> Self::Config {
            let advices = (0..RANGE_W)
                .map(|_| meta.advice_column())
                .collect::<Vec<_>>();

            let range_gate = RangeGate::configure(meta, &advices[..]);
            let vertical_gate =
                VerticalGate::configure(meta, &range_gate, advices.try_into().unwrap());
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

            let rns_base = Rns::construct();
            let rns_scalar = Rns::construct();

            let t0 = start_timer!(|| "witness gen");
            let stack = make_stack::<Emulated, N, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>(
                &rns_base,
                &rns_scalar,
                params.witness_aux,
                params.constant_aux,
                params.pub_key,
                params.message,
                params.r,
                params.s,
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

    fn run_test<
        Emulated: CurveAffine,
        N: PrimeField + Ord,
        const RANGE_W: usize,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    >()
    where
        N: FromUniformBytes<64>,
    {
        // Generate a key pair
        let g = Emulated::generator(); // Generate a key pair
        let sk = Emulated::Scalar::random(OsRng);
        let pub_key = (g * sk).to_affine();

        // Generate a valid signature
        let message = Emulated::Scalar::random(OsRng);

        // Draw arandomness
        let k = Emulated::Scalar::random(OsRng);
        let k_inv = k.invert().unwrap();

        // Calculate `r`
        let r_point = (g * k).to_affine().coordinates().unwrap();
        let x = r_point.x();
        let r: Emulated::Scalar = fe_to_fe(x);

        // Calculate `s`
        let s = k_inv * (message + (r * sk));

        // Sanity check. Ensure we construct a valid signature. So lets verify it
        {
            let s_inv = s.invert().unwrap();
            let u_1 = message * s_inv;
            let u_2 = r * s_inv;
            let r_point = ((g * u_1) + (pub_key * u_2))
                .to_affine()
                .coordinates()
                .unwrap();
            let x_candidate = r_point.x();
            let r_candidate = fe_to_fe(x_candidate);
            assert_eq!(r, r_candidate);
        }

        let witness_aux = Value::known(Emulated::Curve::random(OsRng).into());
        let constant_aux = Emulated::Curve::random(OsRng).into();
        let params = Params {
            witness_aux,
            constant_aux,
            pub_key: Value::known(pub_key),
            r: Value::known(r),
            s: Value::known(s),
            message: Value::known(message),
        };
        let circuit = TestCircuit::<Emulated, N, RANGE_W, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE> {
            params,
            _marker: std::marker::PhantomData,
        };
        let public_inputs = vec![];
        let prover = match MockProver::run(SUBLIMB_SIZE as u32 + 1, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#}"),
        };
        prover.assert_satisfied();
    }

    #[test]
    fn test_ecdsa() {
        run_test::<
            EqAffine,
            Fr,
            2,
            3,  // number of limbs
            90, // limb size
            18, // sublimb size
        >();
    }
}
