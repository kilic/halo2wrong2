use crate::chip::first_degree::FirstDegreeChip;
use crate::chip::range::RangeChip;
use crate::chip::second_degree::SecondDegreeChip;
use crate::chip::select::SelectChip;
use crate::witness::Composable;
use crate::witness::Term;
use crate::{
    chip::Core,
    stack::Stack,
    utils::big_to_fe,
    witness::{Scaled, SecondDegreeScaled, Witness},
};
use ff::FromUniformBytes;
use ff::PrimeField;
use halo2::circuit::Value;
use halo2::{dev::MockProver, plonk::Circuit};
use num_bigint::{BigUint, RandBigInt};
use num_traits::One;
use rand_core::OsRng;

macro_rules! v {
    ($e:expr) => {
        Value::known($e)
    };
}

mod rom;
mod vanilla;
mod vertical;

pub(crate) fn rand_value<F: PrimeField>() -> Value<F> {
    let value = F::random(OsRng);
    v!(value)
}

pub(crate) fn rand_value_in_range<F: PrimeField>(bit_size: usize) -> Value<F> {
    let u = &OsRng.gen_biguint_below(&(BigUint::one() << bit_size));
    v!(big_to_fe(u))
}

pub(crate) fn _max_value_in_range<F: PrimeField>(bit_size: usize) -> Value<F> {
    let u = BigUint::one() << bit_size;
    v!(big_to_fe(&u))
}

impl<F: PrimeField + Ord, const ROM_W: usize> Stack<F, ROM_W> {
    pub(crate) fn _assign_witness(&mut self, w: &Witness<F>) {
        let e = crate::enforcement::FirstDegree::new(vec![w.add(), w.sub()], F::ZERO);
        self.first_degree.push(e);
    }

    pub(crate) fn _rand_witness(&mut self) -> Witness<F> {
        let value = rand_value();
        self.new_witness(value)
    }

    pub(crate) fn assign_rand_witness(&mut self) -> Witness<F> {
        let value = rand_value();
        self.assign(value)
    }

    pub(crate) fn _bad_witness_in_range(&mut self, bit_size: usize) -> Witness<F> {
        let w: Value<F> = _max_value_in_range(bit_size);
        let w = w.map(|v| v + F::ONE);
        self.new_witness(w)
    }

    pub(crate) fn rand_witness_in_range(&mut self, bit_size: usize) -> Witness<F> {
        let value = rand_value_in_range(bit_size);
        self.new_witness(value)
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

pub fn rand_stack_first_degree<F: PrimeField + Ord>(stack: &mut Stack<F, 0>, use_constants: bool) {
    let rand = || F::random(OsRng);

    let w0 = rand_value();
    let w0 = &stack.assign(w0);
    stack.equal(w0, w0);

    for n_terms in 1..20 {
        let mut terms: Vec<Scaled<F>> = (0..n_terms).map(|_| stack.rand_scaled()).collect();
        let constant = if use_constants { rand() } else { F::ZERO };

        // let expected = Scaled::sum(&terms[..], constant);
        let result0 = stack.compose(&terms[..], constant);

        let result1 = Scaled::sum(&terms[..], constant);
        let result1 = stack.assign(result1);
        stack.equal(&result0, &result1);

        terms.push(result1 * -F::ONE);
        stack.zero_sum(&terms[..], constant);
    }
}

pub fn rand_stack_range<F: PrimeField + Ord>(stack: &mut Stack<F, 0>) {
    const LIMB_SIZE: usize = 8;
    for word_size in 1..31 {
        for _ in 0..11 {
            let witness = stack.rand_witness_in_range(word_size);
            stack.decompose(witness.value(), word_size, LIMB_SIZE);
        }
    }
}

pub fn rand_stack_second_degree<F: PrimeField + Ord>(stack: &mut Stack<F, 0>) {
    let rand = || F::random(OsRng);

    for n_first_degree in 0..20 {
        for n_second_degree in 1..20 {
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
                let expect = Term::sum(&terms[..], constant);
                let expect = &stack.assign(expect);
                let result = stack.compose_second_degree(&terms[..], constant);
                result
                    .value()
                    .zip(expect.value())
                    .map(|(e0, e1)| assert_eq!(e0, e1));
                stack.equal(&result, expect);
            }

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
            let sum: Value<F> = Term::sum(&terms[..], constant);

            let w0 = stack.new_witness(sum);
            let w1 = stack.new_witness(Value::known(F::ONE));
            let factor = -F::ONE;
            let sum = SecondDegreeScaled::new(&w0, &w1, factor).into();
            terms.push(sum);
            stack.zero_sum_second_degree(&terms[..], constant);
        }
    }
}

fn rand_arithmetic<F: PrimeField + Ord>() -> Stack<F, 0> {
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
    }
    stack
}

pub(crate) fn run_test<F: Ord + FromUniformBytes<64>, ConcreteCircuit: Circuit<F>>(
    k: u32,
    circuit: &ConcreteCircuit,
) {
    let public_inputs: Vec<Vec<F>> = vec![];
    let prover =
        match MockProver::run(k, circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{e:#?}"),
        };
    prover.assert_satisfied();
}
