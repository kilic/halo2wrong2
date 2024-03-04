use circuitry::{
    utils::{big_to_fe, big_to_fe_unsafe, compose, decompose, decompose_into, fe_to_big},
    witness::{Composable, Witness},
};
use ff::PrimeField;
use halo2::circuit::Value;
use num_bigint::BigUint;
use std::marker::PhantomData;

#[derive(Debug)]
pub enum Range {
    Remainder,
    Operand,
    Unreduced,
    MulQuotient,
}

pub struct UnassignedInteger<W: PrimeField, N: PrimeField> {
    limbs: Vec<Value<N>>,
    big: Value<BigUint>,
    _marker: PhantomData<W>,
}

impl<W: PrimeField, N: PrimeField> UnassignedInteger<W, N> {
    pub fn from_big(big: Value<BigUint>, number_of_limbs: usize, limb_size: usize) -> Self {
        let limbs = big.clone().map(|big| {
            decompose(&big, number_of_limbs, limb_size)
                .iter()
                .map(big_to_fe_unsafe)
                .collect::<Vec<_>>()
        });
        Self {
            limbs: limbs.transpose_vec(number_of_limbs),
            big,
            _marker: PhantomData,
        }
    }

    pub fn from_limbs(limbs: Value<Vec<N>>, number_of_limbs: usize, limb_size: usize) -> Self {
        let big = limbs.as_ref().map(|limbs| {
            let limbs = limbs.iter().map(fe_to_big).collect::<Vec<_>>();
            compose(&limbs, limb_size)
        });
        Self {
            limbs: limbs.transpose_vec(number_of_limbs),
            big,
            _marker: PhantomData,
        }
    }

    pub fn from_fe(wrong: Value<W>, number_of_limbs: usize, limb_size: usize) -> Self {
        let limbs = wrong.map(|e| decompose_into::<W, N>(&e, number_of_limbs, limb_size));
        Self::from_limbs(limbs, number_of_limbs, limb_size)
    }

    pub fn limbs(&self) -> &[Value<N>] {
        &self.limbs
    }

    pub(crate) fn big(&self) -> Value<BigUint> {
        self.big.clone()
    }
}

#[derive(Clone)]
pub struct Integer<W: PrimeField, N: PrimeField> {
    pub(crate) limbs: Vec<Witness<N>>,
    max_vals: Vec<BigUint>,
    big: Value<BigUint>,
    native: Witness<N>,
    limb_size: usize,
    _marker: PhantomData<W>,
}

impl<W: PrimeField, N: PrimeField> std::fmt::Debug for Integer<W, N> {
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

impl<W: PrimeField, N: PrimeField> Integer<W, N> {
    pub fn new(
        limbs: &[Witness<N>],
        max_vals: &[BigUint],
        big: Value<BigUint>,
        native: Witness<N>,
        limb_size: usize,
    ) -> Self {
        #[cfg(feature = "prover-sanity")]
        {
            let number_of_limbs = limbs.len();
            let limbs = limbs.iter().map(|limb| limb.value());
            let limbs: Value<Vec<_>> = Value::from_iter(limbs);
            let expect =
                UnassignedInteger::<W, N>::from_limbs(limbs, number_of_limbs, limb_size).big();
            expect.zip(big.clone()).map(|(a, b)| assert_eq!(a, b));

            big.clone()
                .zip(native.value())
                .map(|(a, b)| assert_eq!(b, big_to_fe(&a)));
        }

        Self {
            limbs: limbs.to_vec(),
            max_vals: max_vals.to_vec(),
            native,
            big,
            limb_size,
            _marker: PhantomData,
        }
    }

    pub fn limbs(&self) -> &[Witness<N>] {
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

    pub fn max_vals(&self) -> &[BigUint] {
        &self.max_vals
    }

    pub fn max(&self) -> BigUint {
        compose(&self.max_vals, self.limb_size)
    }

    pub fn value(&self) -> Value<W> {
        self.big.clone().map(|a| big_to_fe(&a))
    }
}

#[derive(Debug, Clone)]
pub struct ConstantInteger<W: PrimeField, N: PrimeField> {
    limbs: Vec<N>,
    big_limbs: Vec<BigUint>,
    native: N,
    big: BigUint,
    _marker: PhantomData<W>,
}
impl<W: PrimeField, N: PrimeField> ConstantInteger<W, N> {
    pub fn from_big(big: BigUint, number_of_limbs: usize, limb_size: usize) -> Self {
        let native: N = big_to_fe(&big);
        let big_limbs = decompose(&big, number_of_limbs, limb_size);
        let limbs = big_limbs
            .iter()
            .map(|e| big_to_fe_unsafe(e))
            .collect::<Vec<_>>();

        Self {
            big,
            limbs,
            big_limbs,
            native,
            _marker: PhantomData,
        }
    }

    pub fn from_fe(e: &W, number_of_limbs: usize, limb_size: usize) -> Self {
        let big = fe_to_big(e);
        Self::from_big(big, number_of_limbs, limb_size)
    }

    pub fn big(&self) -> &BigUint {
        &self.big
    }

    pub fn native(&self) -> N {
        self.native
    }

    pub fn limbs(&self) -> &[N] {
        &self.limbs
    }

    pub fn big_limbs(&self) -> &[BigUint] {
        &self.big_limbs
    }

    pub fn value(&self) -> W {
        big_to_fe(&self.big)
    }
}
