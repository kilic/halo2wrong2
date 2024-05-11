use crate::circuitry::{
    chip::first_degree::FirstDegreeChip,
    gates::{range::RangeGate, vanilla::VanillaGate, vertical::VerticalGate},
    stack::Stack,
    LayoutCtx,
};
use crate::utils::{big_to_fe, modulus};
use ff::{FromUniformBytes, PrimeField};
use halo2::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{Circuit, ConstraintSystem, Error},
};
use num_bigint::{BigUint, RandBigInt};
use num_traits::{One, Zero};
use rand_core::OsRng;
use std::marker::PhantomData;

use crate::integer::{
    chip::IntegerChip,
    rns::Rns,
    {ConstantInteger, Range, UnassignedInteger},
};

impl<W: PrimeField, N: PrimeField> Rns<W, N> {
    pub fn modulus(&self) -> UnassignedInteger<W, N> {
        UnassignedInteger::from_big(
            Value::known(modulus::<W>()),
            self.number_of_limbs,
            self.limb_size,
        )
    }

    pub fn from_fe(&self, e: Value<W>) -> UnassignedInteger<W, N> {
        UnassignedInteger::from_fe(e, self.number_of_limbs, self.limb_size)
    }

    pub fn from_big(&self, e: BigUint) -> UnassignedInteger<W, N> {
        UnassignedInteger::from_big(Value::known(e), self.number_of_limbs, self.limb_size)
    }

    pub fn rand_in_field(&self) -> UnassignedInteger<W, N> {
        UnassignedInteger::from_fe(
            Value::known(W::random(OsRng)),
            self.number_of_limbs,
            self.limb_size,
        )
    }

    pub fn rand_in_remainder_range(&self) -> UnassignedInteger<W, N> {
        UnassignedInteger::from_big(
            Value::known(OsRng.gen_biguint(self.max_remainder.bits())),
            self.number_of_limbs,
            self.limb_size,
        )
    }

    pub fn rand_in_operand_range(&self) -> UnassignedInteger<W, N> {
        UnassignedInteger::from_big(
            Value::known(OsRng.gen_biguint(self.max_operand.bits())),
            self.number_of_limbs,
            self.limb_size,
        )
    }

    pub fn rand_in_unreduced_range(&self) -> UnassignedInteger<W, N> {
        self.rand_with_limb_bit_size(self._max_unreduced_limb.bits() as usize)
    }

    pub fn rand_with_limb_bit_size(&self, bit_len: usize) -> UnassignedInteger<W, N> {
        let limbs = (0..self.number_of_limbs)
            .map(|_| {
                let e = &OsRng.gen_biguint(bit_len as u64);
                big_to_fe(e)
            })
            .collect::<Vec<N>>();
        UnassignedInteger::from_limbs(Value::known(limbs), self.number_of_limbs, self.limb_size)
    }

    pub fn rand_constant(&self) -> ConstantInteger<W, N> {
        ConstantInteger::from_fe(&W::random(OsRng), self.number_of_limbs, self.limb_size)
    }

    pub fn zero(&self) -> UnassignedInteger<W, N> {
        UnassignedInteger::from_big(
            Value::known(BigUint::zero()),
            self.number_of_limbs,
            self.limb_size,
        )
    }

    pub fn one(&self) -> UnassignedInteger<W, N> {
        UnassignedInteger::from_big(
            Value::known(BigUint::one()),
            self.number_of_limbs,
            self.limb_size,
        )
    }
}

fn make_stack<W: PrimeField, N: PrimeField + Ord>(
    rns: &Rns<W, N>,
    sublimb_size: usize,
) -> Stack<N> {
    let stack = &mut Stack::default();

    let ch: IntegerChip<W, N> = IntegerChip::new(rns, sublimb_size);

    {
        let zero = ch.rns.zero();
        let zero = ch.range(stack, &zero, Range::Remainder);
        ch.assert_zero(stack, &zero);

        let must_be_one = ch.is_zero(stack, &zero);
        stack.assert_one(&must_be_one);
        let must_be_zero = ch.is_one(stack, &zero);
        stack.assert_zero(&must_be_zero);

        let modulus = ch.rns.modulus();
        let modulus = ch.range(stack, &modulus, Range::Remainder);
        ch.assert_zero(stack, &modulus);

        let must_be_one = ch.is_zero(stack, &modulus);
        stack.assert_one(&must_be_one);
        let must_be_zero = ch.is_one(stack, &modulus);
        stack.assert_zero(&must_be_zero);
    }

    // reduce & assert
    {
        for _ in 0..100 {
            let a0 = ch.rns.rand_in_field();
            let a0 = ch.range(stack, &a0, Range::Remainder);
            ch.assert_in_field(stack, &a0);
        }

        let a0 = ch.rns.rand_in_field();
        let a1 = ch.rns.rand_in_field();
        let a1 = ch.assign(stack, a1, Range::Remainder);
        let a0 = ch.range(stack, &a0, Range::Remainder);
        ch.assert_not_equal(stack, &a0, &a1);
        ch.assert_not_zero(stack, &a0);
        let a1 = ch.reduce(stack, &a0);
        ch.copy_equal(stack, &a0, &a1);
        ch.normal_equal(stack, &a0, &a1);

        let a0 = ch.rns.rand_in_remainder_range();
        let a1 = ch.rns.rand_in_remainder_range();
        let a1 = ch.assign(stack, a1, Range::Remainder);
        let a0 = ch.range(stack, &a0, Range::Remainder);
        ch.assert_not_equal(stack, &a0, &a1);
        ch.assert_not_zero(stack, &a0);
        let a1 = ch.reduce(stack, &a0);
        ch.normal_equal(stack, &a0, &a1);

        let a0 = ch.rns.rand_in_operand_range();
        let a1 = ch.rns.rand_in_operand_range();
        let a0 = ch.range(stack, &a0, Range::Operand);
        let a1 = ch.assign(stack, a1, Range::Operand);
        ch.assert_not_equal(stack, &a0, &a1);
        ch.assert_not_zero(stack, &a0);
        let a1 = ch.reduce(stack, &a0);
        ch.normal_equal(stack, &a0, &a1);

        // let a0 = ch.rns.rand_in_unreduced_range();
        // let a1 = ch.rns.rand_in_unreduced_range();
        // let a0 = ch.assign(stack, a0, Range::Unreduced);
        // let a1 = ch.assign(stack, a1, Range::Unreduced);
        // ch.assert_not_equal(stack, &a0, &a1);
        // ch.assert_not_zero(stack, &a0);
        // let a1 = ch.reduce(stack, &a0);
        // ch.normal_equal(stack, &a0, &a1);

        // let a0 = ch.rns.rand_with_limb_bit_size(rns.limb_size * 3 / 2);
        // let a0 = ch.assign(stack, a0, Range::Unreduced);
        // ch.assert_not_zero(stack, &a0);
        // let a1 = ch.reduce(stack, &a0);
        // ch.normal_equal(stack, &a0, &a1);
    }

    // add
    {
        // add
        let a0 = ch.rns.rand_in_remainder_range();
        let a1 = ch.rns.rand_in_remainder_range();
        let a0 = &ch.range(stack, &a0, Range::Remainder);
        let a1 = &ch.range(stack, &a1, Range::Remainder);

        let u0 = ch.add(stack, a0, a1);
        let u1 = ch.add(stack, a1, a0);

        ch.normal_equal(stack, &u0, &u1);
        u0.value()
            .zip(a0.value())
            .zip(a1.value())
            .map(|((u0, a0), a1)| assert_eq!(u0, a0 + a1));

        // add constant
        let a0 = ch.rns.rand_in_remainder_range();
        let a0 = &ch.range(stack, &a0, Range::Remainder);
        let constant = &ch.rns.rand_constant();
        let u0 = ch.add_constant(stack, a0, constant);
        u0.value()
            .zip(a0.value())
            .map(|(u0, a0)| assert_eq!(u0, a0 + constant.value()));

        // neg
        let a0 = ch.rns.rand_in_remainder_range();
        let a0 = &ch.range(stack, &a0, Range::Remainder);
        let neg_a0 = ch.neg(stack, a0);

        let u0 = ch.add(stack, a0, &neg_a0);
        ch.assert_zero(stack, &u0);

        // sub
        let mut u0 = ch.sub(stack, a0, a1);
        {
            for _ in 0..1000 {
                let t = ch.sub(stack, &u0, a0);

                t.value()
                    .zip(u0.value())
                    .zip(a0.value())
                    .map(|((t, u0), a0)| assert_eq!(t, u0 - a0));
                let u1 = ch.add(stack, &t, a0);
                ch.normal_equal(stack, &u0, &u1);
                u0 = t;
            }
        }
    }

    {
        // mul
        let a0 = ch.rns.rand_in_field();
        let a1 = ch.rns.rand_in_field();
        let a0 = &ch.range(stack, &a0, Range::Remainder);
        let a1 = &ch.range(stack, &a1, Range::Remainder);
        let res = a0.value().zip(a1.value()).map(|(a0, a1)| a0 * a1);
        let u0 = rns.from_fe(res);
        let u0 = ch.range(stack, &u0, Range::Remainder);
        let u1 = ch.mul(stack, a0, a1, &[]);
        ch.copy_equal(stack, &u0, &u1);
        ch.normal_equal(stack, &u0, &u1);
        u1.value()
            .zip(a0.value())
            .zip(a1.value())
            .map(|((u0, a0), a1)| assert_eq!(u0, a0 * a1));

        // mul sub
        let a0 = ch.rns.rand_in_field();
        let a1 = ch.rns.rand_in_field();
        let a0 = &ch.range(stack, &a0, Range::Remainder);
        let a1 = &ch.range(stack, &a1, Range::Remainder);
        let to_sub = ch.rns.rand_in_field();
        let to_sub = ch.range(stack, &to_sub, Range::Remainder);
        let res = a0
            .value()
            .zip(a1.value())
            .zip(to_sub.value())
            .map(|((a0, a1), to_sub)| a0 * a1 - to_sub);
        let u0 = rns.from_fe(res);
        let u0 = ch.range(stack, &u0, Range::Remainder);
        let to_sub = ch.neg(stack, &to_sub);

        let u1 = ch.mul(stack, a0, a1, &[&to_sub]);
        ch.copy_equal(stack, &u0, &u1);
        ch.normal_equal(stack, &u0, &u1);
        u1.value()
            .zip(a0.value())
            .zip(a1.value())
            .zip(to_sub.value())
            .map(|(((u0, a0), a1), to_sub)| assert_eq!(u0, a0 * a1 + to_sub));

        // square
        let a0 = ch.rns.rand_in_field();
        let a0 = &ch.range(stack, &a0, Range::Remainder);
        let res = a0.value().map(|a0| (a0 * a0));
        let u0 = rns.from_fe(res);
        let u0 = ch.range(stack, &u0, Range::Remainder);
        let u1 = ch.square(stack, a0, &[]);

        ch.copy_equal(stack, &u0, &u1);
        ch.normal_equal(stack, &u0, &u1);
        u1.value()
            .zip(a0.value())
            .map(|(u0, a0)| assert_eq!(u0, a0 * a0));

        // square sub
        let a0 = ch.rns.rand_in_field();
        let a0 = &ch.range(stack, &a0, Range::Remainder);
        let to_sub = ch.rns.rand_in_field();
        let to_sub = ch.range(stack, &to_sub, Range::Remainder);
        let res = a0
            .value()
            .zip(to_sub.value())
            .map(|(a0, to_sub)| a0 * a0 - to_sub);
        let u0 = rns.from_fe(res);
        let u0 = ch.range(stack, &u0, Range::Remainder);
        let to_sub = ch.neg(stack, &to_sub);
        let u1 = ch.square(stack, a0, &[&to_sub]);
        ch.copy_equal(stack, &u0, &u1);
        ch.normal_equal(stack, &u0, &u1);
        u1.value()
            .zip(a0.value())
            .zip(to_sub.value())
            .map(|((u0, a0), to_sub)| assert_eq!(u0, a0 * a0 + to_sub));

        // div
        for _ in 0..1 {
            let a0 = ch.rns.rand_in_operand_range();
            let a1 = ch.rns.rand_in_operand_range();
            let a0 = &ch.range(stack, &a0, Range::Operand);
            let a1 = &ch.range(stack, &a1, Range::Operand);
            let res = a0
                .value()
                .zip(a1.value())
                .map(|(a0, a1)| a0 * a1.invert().unwrap());
            let u0 = rns.from_fe(res);
            let u0 = ch.range(stack, &u0, Range::Remainder);
            let u1 = ch.div(stack, a0, a1);
            ch.copy_equal(stack, &u0, &u1);
            ch.normal_equal(stack, &u0, &u1);
        }

        // mul div add
        let a0 = ch.rns.rand_in_operand_range();
        let a1 = ch.rns.rand_in_operand_range();
        let divisor = ch.rns.rand_in_operand_range();
        let to_add = ch.rns.rand_in_remainder_range();

        let a0 = &ch.range(stack, &a0, Range::Operand);
        let a1 = &ch.range(stack, &a1, Range::Operand);
        let divisor = &ch.range(stack, &divisor, Range::Operand);
        let to_add = ch.range(stack, &to_add, Range::Remainder);
        let u1 = ch.neg_mul_div(stack, a0, a1, divisor, &[&to_add]);

        let res = a0
            .value()
            .zip(a1.value())
            .zip(to_add.value())
            .zip(divisor.value())
            .map(|(((a0, a1), to_add), divisor)| {
                (a0 * a1 + to_add) * divisor.invert().unwrap().neg()
            });

        let u0 = rns.from_fe(res);
        let u0 = ch.range(stack, &u0, Range::Remainder);

        u1.value()
            .zip(a0.value())
            .zip(a1.value())
            .zip(to_add.value())
            .zip(divisor.value())
            .map(|((((u0, a0), a1), to_add), divisor)| {
                assert_eq!(divisor.neg() * u0, a0 * a1 + to_add)
            });

        ch.copy_equal(stack, &u0, &u1);
        ch.normal_equal(stack, &u0, &u1);
    }

    stack.clone()
}

#[derive(Clone)]
struct TestConfig<N: PrimeField + Ord, const RANGE_W: usize> {
    vertical_gate: VerticalGate<RANGE_W>,
    vanilla_gate: VanillaGate,
    range_gate: RangeGate,
    stack: Stack<N>,
}

#[derive(Default, Clone)]
struct Params {
    limb_size: usize,
    sublimb_size: usize,
}

#[derive(Clone, Default)]
struct TestCircuit<W: PrimeField, N: PrimeField + Ord, const RANGE_W: usize> {
    params: Params,
    _marker: PhantomData<(N, W)>,
}

impl<W: PrimeField, N: PrimeField + Ord, const RANGE_W: usize> Circuit<N>
    for TestCircuit<W, N, RANGE_W>
{
    type Config = TestConfig<N, RANGE_W>;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = Params;

    fn configure_with_params(meta: &mut ConstraintSystem<N>, params: Self::Params) -> Self::Config {
        let rns = Rns::construct(params.limb_size);

        let advices = (0..RANGE_W)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>();
        let range_gate = RangeGate::configure(meta, &advices);
        let vertical_gate = VerticalGate::configure(meta, &range_gate, advices.try_into().unwrap());
        let vanilla_gate = VanillaGate::configure(meta);
        let stack = make_stack::<W, N>(&rns, params.sublimb_size);

        Self::Config {
            stack,
            range_gate,
            vertical_gate,
            vanilla_gate,
        }
    }

    fn configure(_meta: &mut ConstraintSystem<N>) -> Self::Config {
        unreachable!();
    }

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn synthesize(&self, mut cfg: Self::Config, ly: impl Layouter<N>) -> Result<(), Error> {
        let ly_ctx = &mut LayoutCtx::new(ly);
        cfg.stack.layout_first_degree(ly_ctx, &cfg.vanilla_gate)?;
        cfg.stack.layout_second_degree(ly_ctx, &cfg.vanilla_gate)?;
        cfg.stack.layout_selections(ly_ctx, &cfg.vanilla_gate)?;
        cfg.stack.layout_range_limbs(ly_ctx, &cfg.vertical_gate)?;
        cfg.stack.layout_range_single(ly_ctx, &cfg.vertical_gate)?;
        cfg.stack.layout_range_tables(ly_ctx, &cfg.range_gate)?;
        cfg.stack.apply_indirect_copy(ly_ctx)?;

        Ok(())
    }

    fn params(&self) -> Self::Params {
        self.params.clone()
    }
}

fn run_test<W: PrimeField, N: Ord + FromUniformBytes<64>, const RANGE_W: usize>(
    limb_size: usize,
    sublimb_size: usize,
) {
    let circuit = TestCircuit::<W, N, RANGE_W> {
        params: Params {
            limb_size,
            sublimb_size,
        },
        _marker: PhantomData,
    };
    let public_inputs = vec![];
    let prover = match MockProver::run(sublimb_size as u32 + 1, &circuit, public_inputs) {
        Ok(prover) => prover,
        Err(e) => panic!("{e:#}"),
    };
    prover.assert_satisfied();
}

#[test]
fn test_integer() {
    use halo2::halo2curves::pasta::{Fp as PastaFp, Fq as PastaFq};

    let limb_size = 90;
    let sublimb_size = 18;
    run_test::<PastaFp, PastaFq, 2>(limb_size, sublimb_size);
}
