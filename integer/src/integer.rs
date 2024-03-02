use std::marker::PhantomData;

use circuitry::{
    utils::{big_to_fe, big_to_fe_unsafe, compose, decompose, decompose_into, fe_to_big},
    witness::{Composable, Witness},
};
use ff::PrimeField;
use halo2::circuit::Value;
use num_bigint::BigUint;

#[derive(Debug)]
pub enum Range {
    Remainder,
    Operand,
    Unreduced,
    MulQuotient,
}

pub struct UnassignedInteger<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
> {
    limbs: [Value<N>; NUMBER_OF_LIMBS],
    big: Value<BigUint>,
    _marker: PhantomData<W>,
}

impl<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>
    UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>
{
    pub fn from_big(big: Value<BigUint>) -> Self {
        let limbs = big.clone().map(|big| {
            decompose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&big)
                .iter()
                .map(big_to_fe_unsafe)
                .collect::<Vec<_>>()
                .try_into()
                .unwrap()
        });
        Self {
            limbs: limbs.transpose_array(),
            big,
            _marker: PhantomData,
        }
    }

    pub fn from_limbs(limbs: Value<[N; NUMBER_OF_LIMBS]>) -> Self {
        let big = limbs.map(|limbs| {
            let limbs = limbs.iter().map(fe_to_big).collect::<Vec<_>>();
            compose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&limbs.try_into().unwrap())
        });
        Self {
            limbs: limbs.transpose_array(),
            big,
            _marker: PhantomData,
        }
    }

    pub fn from_fe(wrong: Value<W>) -> Self {
        let limbs = wrong.map(|e| decompose_into::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>(&e));
        Self::from_limbs(limbs)
    }

    pub fn limbs(&self) -> &[Value<N>; NUMBER_OF_LIMBS] {
        &self.limbs
        // self.limbs.transpose_vec(NUMBER_OF_LIMBS)
    }

    pub(crate) fn big(&self) -> Value<BigUint> {
        self.big.clone()
    }
}

#[derive(Clone)]
pub struct Integer<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
> {
    pub(crate) limbs: [Witness<N>; NUMBER_OF_LIMBS],
    max_vals: [BigUint; NUMBER_OF_LIMBS],
    big: Value<BigUint>,
    native: Witness<N>,
    _marker: PhantomData<W>,
}

impl<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>
    std::fmt::Debug for Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug = f.debug_struct("Integer");

        self.big.as_ref().map(|big| {
            debug.field("field:  ", &format!("{:#?}", big_to_fe::<W>(big)));
        });
        self.big.as_ref().map(|big| {
            debug.field(
                "value:  ",
                &format!("{}, 0x{}", big.bits(), big.to_str_radix(16)),
            );
        });
        debug.field(
            "max:    ",
            &format!("{}, 0x{}", self.max().bits(), self.max().to_str_radix(16)),
        );

        self.limbs
            .iter()
            .zip(self.max_vals.iter())
            .enumerate()
            .for_each(|(_, (limb, max))| {
                limb.value().map(|limb| {
                    let value = fe_to_big(&limb);

                    debug.field(
                        "limb:   ",
                        &format!("{}, 0x{}", max.bits(), &value.to_str_radix(16)),
                    );
                });
            });
        debug.finish()
    }
}

impl<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>
    Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>
{
    pub fn new(
        limbs: &[Witness<N>; NUMBER_OF_LIMBS],
        max_vals: &[BigUint; NUMBER_OF_LIMBS],
        big: Value<BigUint>,
        native: Witness<N>,
    ) -> Self {
        #[cfg(feature = "prover-sanity")]
        {
            let limbs = limbs.iter().map(|limb| limb.value());
            let limbs: Value<Vec<_>> = Value::from_iter(limbs);
            let expect = UnassignedInteger::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>::from_limbs(
                limbs.map(|limbs| limbs.try_into().unwrap()),
            )
            .big();
            expect.zip(big.clone()).map(|(a, b)| assert_eq!(a, b));

            big.clone()
                .zip(native.value())
                .map(|(a, b)| assert_eq!(b, big_to_fe(&a)));
        }

        Self {
            limbs: *limbs,
            max_vals: max_vals.clone(),
            native,
            big,
            _marker: PhantomData,
        }
    }

    pub fn limbs(&self) -> &[Witness<N>; NUMBER_OF_LIMBS] {
        &self.limbs
    }

    pub fn limb_at(&self, idx: usize) -> &Witness<N> {
        &self.limbs[idx]
    }

    pub fn native(&self) -> &Witness<N> {
        &self.native
    }

    pub fn big(&self) -> Value<BigUint> {
        self.big.clone()
    }

    pub fn max_vals(&self) -> &[BigUint; NUMBER_OF_LIMBS] {
        &self.max_vals
    }

    pub fn max(&self) -> BigUint {
        compose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&self.max_vals)
    }

    pub fn value(&self) -> Value<W> {
        self.big.clone().map(|a| big_to_fe(&a))
    }
}

#[derive(Debug, Clone)]
pub struct ConstantInteger<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
> {
    limbs: [N; NUMBER_OF_LIMBS],
    big_limbs: [BigUint; NUMBER_OF_LIMBS],
    native: N,
    big: BigUint,
    _marker: PhantomData<W>,
}
impl<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>
    ConstantInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>
{
    pub fn from_big(big: BigUint) -> Self {
        let native: N = big_to_fe(&big);
        let big_limbs = decompose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&big);
        let limbs: [N; NUMBER_OF_LIMBS] = big_limbs
            .iter()
            .map(|e| big_to_fe_unsafe(e))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        Self {
            big,
            limbs,
            big_limbs,
            native,
            _marker: PhantomData,
        }
    }

    pub fn from_fe(e: &W) -> Self {
        let big = fe_to_big(e);
        Self::from_big(big)
    }

    pub fn big(&self) -> &BigUint {
        &self.big
    }

    pub fn native(&self) -> N {
        self.native
    }

    pub fn limbs(&self) -> &[N; NUMBER_OF_LIMBS] {
        &self.limbs
    }

    pub fn big_limbs(&self) -> &[BigUint; NUMBER_OF_LIMBS] {
        &self.big_limbs
    }

    pub fn value(&self) -> W {
        big_to_fe(&self.big)
    }
}
