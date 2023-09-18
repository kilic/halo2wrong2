use crate::chip::first_degree::FirstDegreeChip;
use crate::chip::second_degree::SecondDegreeChip;
use ff::PrimeField;
use halo2::circuit::Value;
use num_bigint::{BigUint, RandBigInt};
use num_traits::One;
use rand_core::OsRng;

use crate::{
    chip::Core,
    enforcement::FirstDegreeComposition,
    stack::Stack,
    utils::big_to_fe,
    witness::{Scaled, SecondDegreeScaled, Witness},
};

use std::marker::PhantomData;

use ff::FromUniformBytes;
use halo2::{
    circuit::{Layouter, SimpleFloorPlanner},
    dev::MockProver,
    halo2curves::pasta::Fp,
    plonk::{Circuit, ConstraintSystem, Error},
};

use crate::{
    gates::{
        range::{
            in_place::{NoRangeInPlaceGate, RangeInPlaceGate},
            RangeInPlace,
        },
        vertical::VerticalGate,
    },
    witness::Composable,
    LayoutCtx,
};

macro_rules! v {
    ($e:expr) => {
        Value::known($e)
    };
}

pub fn rand_value<F: PrimeField>() -> Value<F> {
    let value = F::random(OsRng);
    v!(value)
}

pub fn rand_value_in_range<F: PrimeField>(bit_size: usize) -> Value<F> {
    let u = &OsRng.gen_biguint_below(&(BigUint::one() << bit_size));
    v!(big_to_fe(u))
}

impl<F: PrimeField + Ord, const MEM_W: usize> Stack<F, MEM_W> {
    pub(crate) fn _assign_witness(&mut self, w: &Witness<F>) {
        let e = FirstDegreeComposition::new(vec![w.add(), w.sub()], F::ZERO);
        self.first_degree_ternary_compositions.push(e);
    }

    pub(crate) fn _rand_witness(&mut self) -> Witness<F> {
        let value = rand_value();
        self.new_witness(value)
    }

    pub(crate) fn assign_rand_witness(&mut self) -> Witness<F> {
        let value = rand_value();
        self.assign(value)
    }

    pub(crate) fn _assign_rand_witness_in_range(&mut self, bit_size: usize) -> Witness<F> {
        let w = self.rand_witness_in_range(bit_size);
        self._assign_witness(&w);
        w
    }

    // pub(crate) fn _assign_bad_witness_in_range(&mut self, bit_size: usize) -> Witness<F> {
    //     let value: Value<F> = _max_value_in_range(bit_size);
    //     let value = value.map(|v| v + F::ONE);
    //     self.new_witness_in_range(value, bit_size)
    // }

    pub(crate) fn rand_witness_in_range(&mut self, bit_size: usize) -> Witness<F> {
        let value = rand_value_in_range(bit_size);
        self.new_witness_in_range(value, bit_size)
    }

    pub(crate) fn rand_scaled(&mut self) -> Scaled<F> {
        let witness = self.new_witness(v!(F::random(OsRng)));
        let factor = F::random(OsRng);
        Scaled::new(&witness, factor)
    }

    pub(crate) fn rand_second_degree_scaled(&mut self) -> SecondDegreeScaled<F> {
        let w0 = self.new_witness(v!(F::random(OsRng)));
        let w1 = self.new_witness(v!(F::random(OsRng)));
        let factor = F::random(OsRng);
        SecondDegreeScaled::new(&w0, &w1, factor)
    }
}

mod test_composition {

    use crate::{
        gates::{
            range::in_place_sparse::RangeInPlaceSpaseGate, vanilla::VanillaGate,
            var_vanilla::VarVanillaGate,
        },
        witness::Term,
    };

    use super::*;

    fn make_stack_first_degree<'a, F: PrimeField + Ord, const LIMB_SIZE: usize>(
        stack: &mut Stack<F, 0>,
        use_constants: bool,
    ) {
        let rand = || F::random(OsRng);

        let w0 = rand_value();
        let w0 = &stack.assign(w0);
        stack.equal(w0, w0);
        // combination first degree
        for n_terms in 1..10 {
            // compose

            let terms: Vec<Scaled<F>> = (0..n_terms)
                .map(|_| stack.rand_witness_in_range(LIMB_SIZE).into())
                .collect();
            let constant = if use_constants { rand() } else { F::ZERO };

            let expected = Scaled::compose(&terms[..], constant);
            let result = &stack.compose(&terms[..], constant);
            result
                .value()
                .zip(expected)
                .map(|(e0, e1)| assert_eq!(e0, e1));
            let expected = &stack.assign(expected);
            stack.equal(expected, result);

            // zero sum

            let mut terms: Vec<Scaled<F>> = (0..n_terms).map(|_| stack.rand_scaled()).collect();
            let constant = if use_constants { rand() } else { F::ZERO };

            let result = Scaled::compose(&terms[..], constant);
            let result: Scaled<_> = stack.new_witness(result).into();
            terms.push(result.neg());
            stack.zero_sum(&terms[..], constant);
        }
    }

    fn make_stack_second_degree<'a, F: PrimeField + Ord>(stack: &mut Stack<F, 0>) {
        let rand = || F::random(OsRng);

        // combination second degree
        for n_first_degree in 0..20 {
            for n_second_degree in 1..20 {
                // compose
                if n_first_degree + n_second_degree != 0 {
                    let first_degree_terms: Vec<Term<F>> = (0..n_first_degree)
                        .map(|_| stack.rand_scaled().into())
                        .collect();
                    let second_degree_terms: Vec<Term<F>> = (0..n_second_degree)
                        .map(|_| stack.rand_second_degree_scaled().into())
                        .collect();
                    let terms: Vec<Term<F>> = first_degree_terms
                        .iter()
                        .chain(second_degree_terms.iter())
                        .cloned()
                        .collect();
                    let constant = rand();
                    let expect = Term::compose(&terms[..], constant);
                    let expect = &stack.assign(expect);
                    let result = stack.compose_second_degree(&terms[..], constant);
                    result
                        .value()
                        .zip(expect.value())
                        .map(|(e0, e1)| assert_eq!(e0, e1));
                    stack.equal(&result, expect);
                }

                // zero sum
                let first_degree_terms: Vec<Term<F>> = (0..n_first_degree)
                    .map(|_| stack.rand_scaled().into())
                    .collect();
                let second_degree_terms: Vec<Term<F>> = (0..n_second_degree)
                    .map(|_| stack.rand_second_degree_scaled().into())
                    .collect();
                let mut terms: Vec<Term<F>> = first_degree_terms
                    .iter()
                    .chain(second_degree_terms.iter())
                    .cloned()
                    .collect();
                let constant = rand();
                let sum: Value<F> = Term::compose(&terms[..], constant);

                let w0 = stack.new_witness(sum);
                let w1 = stack.new_witness(Value::known(F::ONE));
                let factor = -F::ONE;
                let sum = SecondDegreeScaled::new(&w0, &w1, factor).into();
                terms.push(sum);
                stack.zero_sum_second_degree(&terms[..], constant);
            }
        }
    }

    #[derive(Clone)]
    struct TestConfigVertical<F: PrimeField + Ord, R: RangeInPlace<F, 1>> {
        vertical_gate: VerticalGate<F, R>,
    }

    struct TestCircuitVertical<F: PrimeField + Ord, R: RangeInPlace<F, 1>> {
        _marker: PhantomData<(F, R)>,
    }

    impl<F: PrimeField + Ord, R: RangeInPlace<F, 1>> Circuit<F> for TestCircuitVertical<F, R> {
        type Config = TestConfigVertical<F, R>;
        type FloorPlanner = SimpleFloorPlanner;

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice = meta.advice_column();
            let range_gate = R::configure(meta, [advice]);

            let acc = meta.advice_column();
            let scale = meta.fixed_column();

            let mut vertical_gate = VerticalGate::new(meta, range_gate, scale, advice, acc);
            vertical_gate.configure_composition_gate(meta);

            Self::Config { vertical_gate }
        }

        fn without_witnesses(&self) -> Self {
            Self {
                _marker: PhantomData,
            }
        }

        fn synthesize(&self, cfg: Self::Config, ly: impl Layouter<F>) -> Result<(), Error> {
            let mut stack: Stack<F, 0> = Stack::default();
            make_stack_first_degree::<_, 8>(&mut stack, false);
            let ly = &mut LayoutCtx::new(ly);

            stack.layout_first_degree_compositions(ly, &cfg.vertical_gate)?;
            stack.layout_first_degree_ternary_compositions(ly, &cfg.vertical_gate)?;
            stack.layout_range_compositions(ly, &cfg.vertical_gate)?;
            stack.layout_range_tables(ly, &cfg.vertical_gate)?;
            stack.apply_indirect_copies(ly)?;
            Ok(())
        }
    }

    fn run_test_vertical<F: Ord + FromUniformBytes<64>, R: RangeInPlace<F, 1>>() {
        const K: u32 = 17;
        let circuit = TestCircuitVertical::<F, R> {
            _marker: PhantomData::<(F, R)>,
        };
        let public_inputs: Vec<Vec<F>> = vec![];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };
        prover.assert_satisfied();
    }

    #[test]
    fn test_vertical_composition() {
        run_test_vertical::<Fp, NoRangeInPlaceGate>();
        run_test_vertical::<Fp, RangeInPlaceGate<_, 1>>();
        run_test_vertical::<Fp, RangeInPlaceSpaseGate<_, 1, 8>>();
    }

    #[derive(Clone)]
    struct TestConfigVanilla<F: PrimeField + Ord> {
        vanilla_gate: VanillaGate<F>,
    }

    struct TestCircuitVanilla<F: PrimeField + Ord> {
        _marker: PhantomData<F>,
    }

    impl<F: PrimeField + Ord> Circuit<F> for TestCircuitVanilla<F> {
        type Config = TestConfigVanilla<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let vanilla_gate = VanillaGate::new(meta);
            vanilla_gate.configure(meta);
            Self::Config { vanilla_gate }
        }

        fn without_witnesses(&self) -> Self {
            Self {
                _marker: PhantomData,
            }
        }

        fn synthesize(&self, cfg: Self::Config, ly: impl Layouter<F>) -> Result<(), Error> {
            let mut stack: Stack<F, 0> = Stack::default();
            make_stack_first_degree::<_, 8>(&mut stack, true);
            make_stack_second_degree::<_>(&mut stack);
            let ly = &mut LayoutCtx::new(ly);

            stack.layout_first_degree_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_first_degree_ternary_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_range_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_second_degree_compositions(ly, &cfg.vanilla_gate)?;
            stack.apply_indirect_copies(ly)?;
            Ok(())
        }
    }

    fn run_test_vanilla<F: Ord + FromUniformBytes<64>>() {
        const K: u32 = 17;
        let circuit = TestCircuitVanilla::<F> {
            _marker: PhantomData::<F>,
        };
        let public_inputs: Vec<Vec<F>> = vec![];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };
        prover.assert_satisfied();
    }

    #[test]
    fn test_vanilla_composition() {
        run_test_vanilla::<Fp>();
    }

    #[derive(Clone)]
    struct TestConfigVarVanilla<F: PrimeField + Ord, const W: usize> {
        vanilla_gate: VarVanillaGate<F, W>,
    }

    struct TestCircuitVarVanilla<F: PrimeField + Ord, const W: usize> {
        _marker: PhantomData<F>,
    }

    impl<F: PrimeField + Ord, const W: usize> Circuit<F> for TestCircuitVarVanilla<F, W> {
        type Config = TestConfigVarVanilla<F, W>;
        type FloorPlanner = SimpleFloorPlanner;

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let vanilla_gate = VarVanillaGate::new(meta);
            vanilla_gate.configure(meta);
            Self::Config { vanilla_gate }
        }

        fn without_witnesses(&self) -> Self {
            Self {
                _marker: PhantomData,
            }
        }

        fn synthesize(&self, cfg: Self::Config, ly: impl Layouter<F>) -> Result<(), Error> {
            let mut stack: Stack<F, 0> = Stack::default();
            make_stack_first_degree::<_, 8>(&mut stack, true);
            make_stack_second_degree::<_>(&mut stack);
            let ly = &mut LayoutCtx::new(ly);

            stack.layout_first_degree_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_first_degree_ternary_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_range_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_second_degree_compositions(ly, &cfg.vanilla_gate)?;
            stack.apply_indirect_copies(ly)?;

            Ok(())
        }
    }

    fn run_test_var_vanilla<F: Ord + FromUniformBytes<64>, const W: usize>() {
        const K: u32 = 17;
        let circuit = TestCircuitVarVanilla::<F, W> {
            _marker: PhantomData::<F>,
        };
        let public_inputs: Vec<Vec<F>> = vec![];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };
        prover.assert_satisfied();
    }

    #[test]
    fn test_var_vanilla_composition() {
        run_test_var_vanilla::<Fp, 4>();
        run_test_var_vanilla::<Fp, 5>();
        run_test_var_vanilla::<Fp, 6>();
        run_test_var_vanilla::<Fp, 7>();
    }
}

mod test_arithmetic {

    use crate::{
        chip::select::SelectChip,
        gates::{select::SelectGate, vanilla::VanillaGate, var_vanilla::VarVanillaGate},
    };

    use super::*;

    fn make_stack<F: PrimeField + Ord>() -> Stack<F, 0> {
        let mut stack = Stack::default();

        let rand = || F::random(OsRng);
        let one = &stack.get_constant(F::ONE);
        let zero = &stack.get_constant(F::ZERO);

        stack.assert_one(one);
        stack.assert_zero(zero);
        stack.assert_bit(zero);
        stack.assert_bit(one);
        let rand_constant = rand();

        // equality
        {
            let w0 = &stack.assign_rand_witness();
            stack.equal(w0, w0);
            stack.assert_not_zero(w0);
            let w1 = &stack.assign_rand_witness();
            stack.assert_not_equal(w0, w1);
        }

        // constant registry
        {
            let c0 = rand();
            let w0 = &stack.get_constant(c0);
            let w0_constant = &stack.get_constant(c0);
            stack.equal(w0_constant, w0);
            stack.equal_to_constant(w0, c0);
        }

        // arithmetic
        {
            let x0 = rand();
            let x1 = rand();
            let w0 = &stack.assign(v!(x0));
            let w1 = &stack.assign(v!(x1));

            // add
            let w0w1 = &stack.add(w0, w1);
            let w1w0 = &stack.add(w1, w0);
            stack.equal(w0w1, w1w0);
            stack.equal_to_constant(w0w1, x0 + x1);
            let must_be_w0w1 = &stack.add_constant(w0, x1);
            stack.equal(must_be_w0w1, w0w1);

            // sub
            let u = &stack.sub(w0, w1);
            stack.equal_to_constant(u, x0 - x1);
            let must_be_w0 = &stack.sub(w0w1, w1);
            let must_be_w1 = &stack.sub(w0w1, w0);
            stack.equal(must_be_w0, w0);
            stack.equal(must_be_w1, w1);
            let neg_w1 = &stack.sub_from_constant(x0, w0w1);
            let must_be_zero = stack.add(neg_w1, w1);
            stack.assert_zero(&must_be_zero);
            let neg_w0 = &stack.sub_from_constant(x1, w0w1);
            let must_be_zero = stack.add(neg_w0, w0);
            stack.assert_zero(&must_be_zero);
            let must_be_c = stack.sub_and_add_constant(w0, w0, rand_constant);
            stack.equal_to_constant(&must_be_c, rand_constant);

            // mul
            let w0w1 = &stack.mul(w0, w1);
            stack.equal_to_constant(w0w1, x0 * x1);
            let w1w0 = &stack.mul(w1, w0);
            stack.equal(w0w1, w1w0);
            Scaled::new(w0, x1);
            let must_be_w0w1 = &stack.scale(Scaled::new(w0, x1));
            stack.equal(must_be_w0w1, w0w1);
            let must_be_w0w1 = &stack.scale(Scaled::new(w1, x0));
            stack.equal(must_be_w0w1, w0w1);
            let factor = rand();
            let u = stack.mul_add_constant_scaled(factor, w0, w1, rand_constant);
            stack.equal_to_constant(&u, factor * x0 * x1 + rand_constant);

            // div
            let must_be_w1 = &stack.div_incomplete(w0w1, w0);
            stack.equal(must_be_w1, w1);
            let must_be_w0 = &stack.div_incomplete(w0w1, w1);
            stack.equal(must_be_w0, w0);

            // inv
            let inv_w0 = &stack.inv_incomplete(w0);
            let must_be_one = &stack.mul(w0, inv_w0);
            stack.assert_one(must_be_one);
            let (inv_w0, sign_must_be_zero) = &stack.inv(w0);
            let must_be_one = &stack.mul(w0, inv_w0);
            stack.assert_one(must_be_one);
            stack.assert_zero(sign_must_be_zero);
            let (result_must_be_one, sign_must_be_one) = &stack.inv(zero);
            stack.assert_one(sign_must_be_one);
            stack.assert_one(result_must_be_one);
        }

        // bit assertation
        {
            // assigned
            stack.assert_bit(one);
            stack.assert_bit(zero);
            // unassigned
            let w0 = &stack.new_witness(v!(F::ONE));
            stack.assert_bit(w0);
            stack.assert_one(w0);
            let w0 = &stack.new_witness(v!(F::ZERO));
            stack.assert_bit(w0);
            stack.assert_zero(w0);
        }

        // selection
        {
            // select

            let w0 = &stack.assign_rand_witness();
            let w1 = &stack.assign_rand_witness();
            let selected = &stack.select(one, w0, w1);
            stack.equal(selected, w0);
            let selected = &stack.select(zero, w0, w1);
            stack.equal(selected, w1);
            // // select or assign
            // let w0 = &stack.assign_rand_witness();
            // let constant = rand();
            // let selected = &stack.select_or_assign(one, w0, constant);
            // stack.equal(selected, w0);
            // let selected = &stack.select_or_assign(zero, w0, constant);
            // stack.equal_to_constant(selected, constant);
            // let c0 = rand();
            // let c1 = rand();
            // let selected = &stack.select_constant(one, c0, c1);
            // stack.equal_to_constant(selected, c0);
            // let selected = &stack.select_constant(zero, c0, c1);
            // stack.equal_to_constant(selected, c1);
        }
        stack
    }

    #[derive(Clone)]
    struct TestConfigVanilla<F: PrimeField + Ord> {
        vanilla_gate: VanillaGate<F>,
        select_gate: SelectGate<F>,
    }

    struct TestCircuitVanilla<F: PrimeField + Ord> {
        _marker: PhantomData<F>,
    }

    impl<F: PrimeField + Ord> Circuit<F> for TestCircuitVanilla<F> {
        type Config = TestConfigVanilla<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let vanilla_gate = VanillaGate::new(meta);
            let shared_advices = vanilla_gate.advice_colums();
            let extra_advice = meta.advice_column();
            let select_gate = SelectGate::new(
                meta,
                shared_advices[0],
                shared_advices[1],
                shared_advices[2],
                extra_advice,
            );
            vanilla_gate.configure(meta);
            select_gate.configure(meta);

            Self::Config {
                vanilla_gate,
                select_gate,
            }
        }

        fn without_witnesses(&self) -> Self {
            Self {
                _marker: PhantomData,
            }
        }

        fn synthesize(&self, cfg: Self::Config, ly: impl Layouter<F>) -> Result<(), Error> {
            let mut stack = make_stack::<_>();
            let ly = &mut LayoutCtx::new(ly);
            stack.layout_first_degree_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_first_degree_ternary_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_range_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_second_degree_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_selections(ly, &cfg.select_gate)?;
            stack.apply_indirect_copies(ly)?;
            Ok(())
        }
    }

    fn run_test_vanilla<F: Ord + FromUniformBytes<64>>() {
        const K: u32 = 17;
        let circuit = TestCircuitVanilla::<F> {
            _marker: PhantomData::<F>,
        };
        let public_inputs: Vec<Vec<F>> = vec![];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };
        prover.assert_satisfied();
    }

    #[test]
    fn test_arithmetic_vanilla() {
        run_test_vanilla::<Fp>();
    }

    #[derive(Clone)]
    struct TestConfigVarVanilla<F: PrimeField + Ord, const W: usize> {
        vanilla_gate: VarVanillaGate<F, W>,
    }

    struct TestCircuitVarVanilla<F: PrimeField + Ord, const W: usize> {
        _marker: PhantomData<F>,
    }

    impl<F: PrimeField + Ord, const W: usize> Circuit<F> for TestCircuitVarVanilla<F, W> {
        type Config = TestConfigVarVanilla<F, W>;
        type FloorPlanner = SimpleFloorPlanner;

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let vanilla_gate = VarVanillaGate::new(meta);
            vanilla_gate.configure(meta);
            Self::Config { vanilla_gate }
        }

        fn without_witnesses(&self) -> Self {
            Self {
                _marker: PhantomData,
            }
        }

        fn synthesize(&self, cfg: Self::Config, ly: impl Layouter<F>) -> Result<(), Error> {
            let mut stack = make_stack::<_>();
            let ly = &mut LayoutCtx::new(ly);

            stack.layout_first_degree_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_first_degree_ternary_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_range_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_second_degree_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_selections(ly, &cfg.vanilla_gate)?;
            stack.apply_indirect_copies(ly)?;

            Ok(())
        }
    }

    fn run_test_var_vanilla<F: Ord + FromUniformBytes<64>, const W: usize>() {
        const K: u32 = 17;
        let circuit = TestCircuitVarVanilla::<F, W> {
            _marker: PhantomData::<F>,
        };
        let public_inputs: Vec<Vec<F>> = vec![];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };
        prover.assert_satisfied();
    }

    #[test]
    fn test_arithmetic_var_vanilla() {
        run_test_var_vanilla::<Fp, 4>();
        run_test_var_vanilla::<Fp, 5>();
        run_test_var_vanilla::<Fp, 6>();
        run_test_var_vanilla::<Fp, 7>();
    }

    fn make_stack_simpler<F: PrimeField + Ord>() -> Stack<F, 0> {
        let mut stack = Stack::default();

        let rand = || F::random(OsRng);

        // equality
        {
            let w0 = &stack.assign_rand_witness();
            stack.equal(w0, w0);
        }

        // arithmetic
        {
            let x0 = rand();
            let x1 = rand();
            let w0 = &stack.assign(v!(x0));
            let w1 = &stack.assign(v!(x1));

            // add
            let w0w1 = &stack.add(w0, w1);
            let w1w0 = &stack.add(w1, w0);
            stack.equal(w0w1, w1w0);

            // sub
            let must_be_w0 = &stack.sub(w0w1, w1);
            let must_be_w1 = &stack.sub(w0w1, w0);
            stack.equal(must_be_w0, w0);
            stack.equal(must_be_w1, w1);
        }

        stack
    }

    #[derive(Clone)]
    struct TestConfigVertical<F: PrimeField + Ord> {
        vertical_gate: VerticalGate<F, NoRangeInPlaceGate>,
    }

    struct TestCircuitVertical<F: PrimeField + Ord> {
        _marker: PhantomData<F>,
    }

    impl<F: PrimeField + Ord> Circuit<F> for TestCircuitVertical<F> {
        type Config = TestConfigVertical<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice = meta.advice_column();
            let acc = meta.advice_column();
            let scale = meta.fixed_column();

            let mut vertical_gate =
                VerticalGate::new(meta, NoRangeInPlaceGate {}, scale, advice, acc);
            vertical_gate.configure_composition_gate(meta);

            Self::Config { vertical_gate }
        }

        fn without_witnesses(&self) -> Self {
            Self {
                _marker: PhantomData,
            }
        }

        fn synthesize(&self, cfg: Self::Config, ly: impl Layouter<F>) -> Result<(), Error> {
            let mut stack = make_stack_simpler::<_>();
            let ly = &mut LayoutCtx::new(ly);
            stack.layout_first_degree_ternary_compositions(ly, &cfg.vertical_gate)?;
            stack.apply_indirect_copies(ly)?;
            Ok(())
        }
    }

    fn run_test_vertical<F: Ord + FromUniformBytes<64>>() {
        const K: u32 = 17;
        let circuit = TestCircuitVertical::<F> {
            _marker: PhantomData::<F>,
        };
        let public_inputs: Vec<Vec<F>> = vec![];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };
        prover.assert_satisfied();
    }

    #[test]
    fn test_vertical() {
        run_test_vertical::<Fp>();
    }
}

mod test_rom {

    use crate::{
        chip::ROMChip,
        gates::{rom::ROMGate, vanilla::VanillaGate},
    };

    use super::*;

    fn make_stack<F: PrimeField + Ord, const MEM_W: usize>() -> Stack<F, MEM_W> {
        let mut stack: Stack<F, MEM_W> = Stack::default();

        let tag = F::random(OsRng);

        let w0 = (0..MEM_W)
            .map(|_| stack.assign_rand_witness())
            .collect::<Vec<_>>();
        let w0: &[Witness<F>; MEM_W] = &w0.try_into().unwrap();

        let w1 = (0..MEM_W)
            .map(|_| stack.assign_rand_witness())
            .collect::<Vec<_>>();
        let w1 = &w1.try_into().unwrap();

        let w2 = (0..MEM_W)
            .map(|_| stack.assign_rand_witness())
            .collect::<Vec<_>>();
        let w2 = &w2.try_into().unwrap();

        let w3 = (0..MEM_W)
            .map(|_| stack.assign_rand_witness())
            .collect::<Vec<_>>();
        let w3 = &w3.try_into().unwrap();

        let a0 = F::from(0);
        let a1 = F::from(1);
        let a2 = F::from(2);
        let a3 = F::from(3);

        stack.write(tag, a0, w0);
        stack.write(tag, a1, w1);
        stack.write(tag, a2, w2);
        stack.write(tag, a3, w3);

        let f0 = &stack.assign(v!(F::from(0)));
        let f1 = &stack.assign(v!(F::from(1)));
        let f2 = &stack.assign(v!(F::from(2)));
        let f3 = &stack.assign(v!(F::from(3)));

        let _w1 = stack.read(tag, F::ZERO, f1);
        w1.iter().zip(_w1.iter()).for_each(|(w, a)| {
            stack.equal(w, a);
        });
        let _w0 = stack.read(tag, F::ZERO, f0);
        w0.iter().zip(_w0.iter()).for_each(|(w, a)| {
            stack.equal(w, a);
        });
        let _w3 = stack.read(tag, F::ZERO, f3);
        w3.iter().zip(_w3.iter()).for_each(|(w, a)| {
            stack.equal(w, a);
        });
        let _w3 = stack.read(tag, F::ZERO, f3);
        w3.iter().zip(_w3.iter()).for_each(|(w, a)| {
            stack.equal(w, a);
        });
        let _w0 = stack.read(tag, F::ZERO, f0);
        w0.iter().zip(_w0.iter()).for_each(|(w, a)| {
            stack.equal(w, a);
        });
        let _w2 = stack.read(tag, F::ZERO, f2);
        w2.iter().zip(_w2.iter()).for_each(|(w, a)| {
            stack.equal(w, a);
        });
        let _w2 = stack.read(tag, F::ZERO, f2);
        w2.iter().zip(_w2.iter()).for_each(|(w, a)| {
            stack.equal(w, a);
        });

        stack
    }

    #[derive(Clone)]
    struct TestConfigVertical<F: PrimeField + Ord> {
        vanilla_gate: VanillaGate<F>,
        rom_gate: ROMGate<F, 3>,
    }

    struct TestCircuitVertical<F: PrimeField + Ord> {
        _marker: PhantomData<F>,
    }

    impl<F: PrimeField + Ord> Circuit<F> for TestCircuitVertical<F> {
        type Config = TestConfigVertical<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let vanilla_gate = VanillaGate::new(meta);
            vanilla_gate.configure(meta);
            let query_values = vanilla_gate.advice_colums();
            let table_values = query_values.clone();
            let query_fraction = meta.advice_column();

            let rom_gate = ROMGate::configure(meta, query_fraction, query_values, table_values);

            Self::Config {
                vanilla_gate,
                rom_gate,
            }
        }

        fn without_witnesses(&self) -> Self {
            Self {
                _marker: PhantomData,
            }
        }

        fn synthesize(&self, cfg: Self::Config, ly: impl Layouter<F>) -> Result<(), Error> {
            let mut stack = make_stack::<_, 3>();
            let ly = &mut LayoutCtx::new(ly);
            stack.layout_first_degree_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_first_degree_ternary_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_second_degree_compositions(ly, &cfg.vanilla_gate)?;
            stack.layout_rom(ly, &cfg.rom_gate)?;
            stack.apply_indirect_copies(ly)?;
            Ok(())
        }
    }

    fn run_test_rom<F: Ord + FromUniformBytes<64>>() {
        const K: u32 = 17;
        let circuit = TestCircuitVertical::<F> {
            _marker: PhantomData::<F>,
        };
        let public_inputs: Vec<Vec<F>> = vec![];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };
        prover.assert_satisfied();
    }

    #[test]
    fn test_rom() {
        run_test_rom::<Fp>();
    }
}
