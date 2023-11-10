use std::marker::PhantomData;

use circuitry::{
    gates::{
        range::{in_place::RangeInPlaceGate, RangeInPlace},
        vanilla::VanillaGate,
        vertical::VerticalGate,
    },
    stack::Stack,
    utils::{big_to_fe, modulus},
    LayoutCtx,
};
use ff::{FromUniformBytes, PrimeField};
use halo2::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{Circuit, ConstraintSystem, Error},
};
use num_bigint::{BigUint, RandBigInt};
use num_traits::{One, Zero};
use rand_core::OsRng;

use crate::{
    chip::IntegerChip,
    integer::{ConstantInteger, Range, UnassignedInteger},
    rns::Rns,
};

impl<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>
    Rns<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>
{
    pub fn modulus(&self) -> UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        UnassignedInteger::from_big(Value::known(modulus::<W>()))
    }

    pub fn from_fe(&self, e: W) -> UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        UnassignedInteger::from_fe(Value::known(e))
    }

    pub fn from_big(&self, e: BigUint) -> UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        UnassignedInteger::from_big(Value::known(e))
    }

    pub fn rand_in_field(&self) -> UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        UnassignedInteger::from_fe(Value::known(W::random(OsRng)))
    }

    pub fn rand_in_remainder_range(&self) -> UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        UnassignedInteger::from_big(Value::known(OsRng.gen_biguint(self.max_remainder.bits())))
    }

    pub fn rand_in_operand_range(&self) -> UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        UnassignedInteger::from_big(Value::known(OsRng.gen_biguint(self.max_operand.bits())))
    }

    pub fn rand_in_unreduced_range(&self) -> UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        self.rand_with_limb_bit_size(self._max_unreduced_limb.bits() as usize)
    }

    pub fn rand_with_limb_bit_size(
        &self,
        bit_len: usize,
    ) -> UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let limbs = (0..NUMBER_OF_LIMBS)
            .map(|_| {
                let e = &OsRng.gen_biguint(bit_len as u64);
                big_to_fe(e)
            })
            .collect::<Vec<N>>();
        UnassignedInteger::from_limbs(Value::known(limbs.try_into().unwrap()))
    }

    pub fn rand_constant(&self) -> ConstantInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        ConstantInteger::from_fe(&W::random(OsRng))
    }

    pub fn zero(&self) -> UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        UnassignedInteger::from_big(Value::known(BigUint::zero()))
    }

    pub fn one(&self) -> UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        UnassignedInteger::from_big(Value::known(BigUint::one()))
    }
}

fn make_stack<
    W: PrimeField,
    N: PrimeField + Ord,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const NUMBER_OF_SUBLIMBS: usize,
    const SUBLIMB_SIZE: usize,
>(
    rns: &Rns<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
) -> Stack<N, 0> {
    let stack = &mut Stack::<N, 0>::default();

    let ch: IntegerChip<W, N, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE> =
        IntegerChip::new(rns);

    {
        let zero = ch.rns.zero();
        let zero = ch.range(stack, zero, Range::Remainder);
        ch.assert_zero(stack, &zero);
        let zero = ch.rns.modulus();
        let zero = ch.range(stack, zero, Range::Remainder);
        ch.assert_zero(stack, &zero);
    }

    // reduce & assert
    {
        let a0 = ch.rns.rand_in_field();
        let a1 = ch.rns.rand_in_field();
        let a1 = ch.assign(stack, a1, Range::Remainder);
        let a0 = ch.range(stack, a0, Range::Remainder);
        ch.assert_not_equal(stack, &a0, &a1);
        ch.assert_not_zero(stack, &a0);
        let a1 = ch.reduce(stack, &a0);
        ch.copy_equal(stack, &a0, &a1);
        ch.normal_equal(stack, &a0, &a1);

        let a0 = ch.rns.rand_in_remainder_range();
        let a1 = ch.rns.rand_in_remainder_range();
        let a1 = ch.assign(stack, a1, Range::Remainder);
        let a0 = ch.range(stack, a0, Range::Remainder);
        ch.assert_not_equal(stack, &a0, &a1);
        ch.assert_not_zero(stack, &a0);
        let a1 = ch.reduce(stack, &a0);
        ch.normal_equal(stack, &a0, &a1);

        let a0 = ch.rns.rand_in_operand_range();
        let a1 = ch.rns.rand_in_operand_range();
        let a0 = ch.range(stack, a0, Range::Operand);
        let a1 = ch.assign(stack, a1, Range::Operand);
        ch.assert_not_equal(stack, &a0, &a1);
        ch.assert_not_zero(stack, &a0);
        let a1 = ch.reduce(stack, &a0);
        ch.normal_equal(stack, &a0, &a1);

        let a0 = ch.rns.rand_in_unreduced_range();
        let a1 = ch.rns.rand_in_unreduced_range();
        let a0 = ch.assign(stack, a0, Range::Unreduced);
        let a1 = ch.assign(stack, a1, Range::Unreduced);
        ch.assert_not_equal(stack, &a0, &a1);
        ch.assert_not_zero(stack, &a0);
        let a1 = ch.reduce(stack, &a0);
        ch.normal_equal(stack, &a0, &a1);

        let a0 = ch.rns.rand_with_limb_bit_size(LIMB_SIZE * 3 / 2);
        let a0 = ch.assign(stack, a0, Range::Unreduced);
        ch.assert_not_zero(stack, &a0);
        let a1 = ch.reduce(stack, &a0);
        ch.normal_equal(stack, &a0, &a1);
    }

    // add
    {
        // add
        let a0 = ch.rns.rand_in_remainder_range();
        let a1 = ch.rns.rand_in_remainder_range();
        let a0 = &ch.range(stack, a0, Range::Remainder);
        let a1 = &ch.range(stack, a1, Range::Remainder);

        let u0 = ch.add(stack, a0, a1);
        let u1 = ch.add(stack, a1, a0);

        ch.normal_equal(stack, &u0, &u1);
        u0.value()
            .zip(a0.value())
            .zip(a1.value())
            .map(|((u0, a0), a1)| assert_eq!(u0, a0 + a1));

        // add constant
        let a0 = ch.rns.rand_in_remainder_range();
        let a0 = &ch.range(stack, a0, Range::Remainder);
        let constant = &ch.rns.rand_constant();
        let u0 = ch.add_constant(stack, a0, constant);
        u0.value()
            .zip(a0.value())
            .map(|(u0, a0)| assert_eq!(u0, a0 + constant.value()));

        // neg
        let a0 = ch.rns.rand_in_remainder_range();
        let a0 = &ch.range(stack, a0, Range::Remainder);
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
        let a0 = &ch.range(stack, a0, Range::Remainder);
        let a1 = &ch.range(stack, a1, Range::Remainder);
        let res = a0.value().zip(a1.value()).map(|(a0, a1)| a0 * a1);
        let u0 = UnassignedInteger::from_fe(res);
        let u0 = ch.range(stack, u0, Range::Remainder);
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
        let a0 = &ch.range(stack, a0, Range::Remainder);
        let a1 = &ch.range(stack, a1, Range::Remainder);
        let to_sub = ch.rns.rand_in_field();
        let to_sub = ch.range(stack, to_sub, Range::Remainder);
        let res = a0
            .value()
            .zip(a1.value())
            .zip(to_sub.value())
            .map(|((a0, a1), to_sub)| a0 * a1 - to_sub);
        let u0 = UnassignedInteger::from_fe(res);
        let u0 = ch.range(stack, u0, Range::Remainder);
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
        let a0 = &ch.range(stack, a0, Range::Remainder);
        let res = a0.value().map(|a0| (a0 * a0));
        let u0 = UnassignedInteger::from_fe(res);
        let u0 = ch.range(stack, u0, Range::Remainder);
        let u1 = ch.square(stack, a0, &[]);

        ch.copy_equal(stack, &u0, &u1);
        ch.normal_equal(stack, &u0, &u1);
        u1.value()
            .zip(a0.value())
            .map(|(u0, a0)| assert_eq!(u0, a0 * a0));

        // square sub
        let a0 = ch.rns.rand_in_field();
        let a0 = &ch.range(stack, a0, Range::Remainder);
        let to_sub = ch.rns.rand_in_field();
        let to_sub = ch.range(stack, to_sub, Range::Remainder);
        let res = a0
            .value()
            .zip(to_sub.value())
            .map(|(a0, to_sub)| a0 * a0 - to_sub);
        let u0 = UnassignedInteger::from_fe(res);
        let u0 = ch.range(stack, u0, Range::Remainder);
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
            // let a0 = ch
            //     .rns
            //     .from_big(BigUint::from(30u32) + &ch.rns.wrong_modulus);
            // let a1 = ch.rns.from_big(BigUint::from(5u32));
            let a0 = &ch.range(stack, a0, Range::Operand);
            let a1 = &ch.range(stack, a1, Range::Operand);
            let res = a0
                .value()
                .zip(a1.value())
                .map(|(a0, a1)| a0 * a1.invert().unwrap());
            let u0 = UnassignedInteger::from_fe(res);
            let u0 = ch.range(stack, u0, Range::Remainder);
            let u1 = ch.div(stack, a0, a1);
            ch.copy_equal(stack, &u0, &u1);
            ch.normal_equal(stack, &u0, &u1);
        }

        // mul div add
        let a0 = ch.rns.rand_in_operand_range();
        let a1 = ch.rns.rand_in_operand_range();
        let divisor = ch.rns.rand_in_operand_range();
        let to_add = ch.rns.rand_in_field();
        let a0 = &ch.range(stack, a0, Range::Operand);
        let a1 = &ch.range(stack, a1, Range::Operand);

        let divisor = &ch.range(stack, divisor, Range::Operand);
        let to_add = ch.range(stack, to_add, Range::Remainder);
        let u1 = ch.neg_mul_div(stack, a0, a1, divisor, &[&to_add]);

        let res = a0
            .value()
            .zip(a1.value())
            .zip(to_add.value())
            .zip(divisor.value())
            .map(|(((a0, a1), to_add), divisor)| {
                (a0 * a1 + to_add) * divisor.invert().unwrap().neg()
            });

        let u0 = UnassignedInteger::from_fe(res);
        let u0 = ch.range(stack, u0, Range::Remainder);

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
struct TestConfig<
    W: PrimeField,
    N: PrimeField + Ord,
    R: RangeInPlace<N, 1>,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const NUMBER_OF_SUBLIMBS: usize,
    const SUBLIMB_SIZE: usize,
> {
    vertical_gate: VerticalGate<N, R>,
    vanilla_gate: VanillaGate<N>,
    rns: Rns<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
}

#[derive(Default)]
struct TestCircuit<
    W: PrimeField,
    N: PrimeField + Ord,
    R: RangeInPlace<N, 1>,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const NUMBER_OF_SUBLIMBS: usize,
    const SUBLIMB_SIZE: usize,
> {
    _marker: PhantomData<(W, N, R)>,
}

impl<
        W: PrimeField,
        N: PrimeField + Ord,
        R: RangeInPlace<N, 1>,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const NUMBER_OF_SUBLIMBS: usize,
        const SUBLIMB_SIZE: usize,
    > Circuit<N>
    for TestCircuit<W, N, R, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>
{
    type Config = TestConfig<W, N, R, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>;
    type FloorPlanner = SimpleFloorPlanner;

    fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
        let rns = Rns::construct();

        let advice = meta.advice_column();
        let range_gate = R::configure(meta, [advice]);

        let acc = meta.advice_column();
        let scale = meta.fixed_column();

        let mut vertical_gate = VerticalGate::new(meta, range_gate, scale, advice, acc);
        vertical_gate.configure_composition_gate(meta);

        let vanilla_gate = VanillaGate::new(meta);
        vanilla_gate.configure(meta);

        Self::Config {
            rns,
            vertical_gate,
            vanilla_gate,
        }
    }

    fn without_witnesses(&self) -> Self {
        Self {
            _marker: PhantomData,
        }
    }

    fn synthesize(&self, cfg: Self::Config, ly: impl Layouter<N>) -> Result<(), Error> {
        let mut stack =
            make_stack::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>(
                &cfg.rns,
            );

        let ly_ctx = &mut LayoutCtx::new(ly);

        stack.layout_first_degree_compositions(ly_ctx, &cfg.vertical_gate)?;

        stack.layout_second_degree_compositions(ly_ctx, &cfg.vanilla_gate)?;
        stack.layout_first_degree_ternary_compositions(ly_ctx, &cfg.vanilla_gate)?;
        stack.layout_range_compositions(ly_ctx, &cfg.vanilla_gate)?;
        stack.layout_selections(ly_ctx, &cfg.vanilla_gate)?;

        stack.layout_range_tables(ly_ctx, &cfg.vertical_gate)?;

        stack.apply_indirect_copies(ly_ctx)?;

        Ok(())
    }
}

fn run_test<
    W: PrimeField,
    N: Ord + FromUniformBytes<64>,
    R: RangeInPlace<N, 1>,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const NUMBER_OF_SUBLIMBS: usize,
    const SUBLIMB_SIZE: usize,
>(
    k: u32,
) {
    let circuit =
        TestCircuit::<W, N, R, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE> {
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
fn test_integer() {
    use halo2::halo2curves::pasta::{Fp as PastaFp, Fq as PastaFq};

    run_test::<
        PastaFp,
        PastaFq,
        RangeInPlaceGate<PastaFq, 1>,
        3,  // number of limbs
        90, // limb size
        5,  // number of sublimbs
        18, // sublimb size
    >(19);
}
