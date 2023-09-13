use std::marker::PhantomData;

use circuitry::{
    utils::{big_to_fe, big_to_fe_unsafe, compose, decompose, decompose_into, fe_to_big},
    witness::Witness,
};
use ff::PrimeField;
use halo2::circuit::Value;
use num_bigint::BigUint;

#[derive(Debug)]
pub enum Range {
    Remainder,
    Operand,
    MulQuotient,
    #[cfg(test)]
    Unreduced,
}

pub struct UnassignedInteger<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
> {
    pub(crate) limbs: Value<[N; NUMBER_OF_LIMBS]>,
    pub(crate) big: Value<BigUint>,
    _marker: PhantomData<W>,
}

impl<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>
    From<Value<BigUint>> for UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>
{
    fn from(big: Value<BigUint>) -> Self {
        let limbs = big.clone().map(|big| {
            decompose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&big)
                .iter()
                .map(big_to_fe_unsafe)
                .collect::<Vec<_>>()
                .try_into()
                .unwrap()
        });
        Self {
            limbs,
            big,
            _marker: PhantomData,
        }
    }
}

impl<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>
    UnassignedInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>
{
    pub fn from_limbs(limbs: Value<[N; NUMBER_OF_LIMBS]>) -> Self {
        let big = limbs.map(|limbs| {
            let limbs = limbs.iter().map(fe_to_big).collect::<Vec<_>>();
            compose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&limbs.try_into().unwrap())
        });
        Self {
            limbs,
            big,
            _marker: PhantomData,
        }
    }

    pub fn from_fe(wrong: Value<W>) -> Self {
        let limbs = wrong.map(|e| decompose_into::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>(&e));
        Self::from_limbs(limbs)
    }

    pub fn limbs(&self) -> &Value<[N; NUMBER_OF_LIMBS]> {
        &self.limbs
    }

    pub(crate) fn big(&self) -> Value<BigUint> {
        self.big.clone()
    }
}

#[derive(Clone, Debug)]
pub struct Integer<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
> {
    pub(crate) limbs: [Witness<N>; NUMBER_OF_LIMBS],
    pub(crate) max_vals: [BigUint; NUMBER_OF_LIMBS],
    pub(crate) big: Value<BigUint>,
    pub(crate) native: Witness<N>,
    _marker: PhantomData<W>,
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
        #[cfg(feature = "sanity-check")]
        {
            let limbs = limbs.iter().map(|limb| limb.value());
            let limbs: Value<Vec<_>> = Value::from_iter(limbs);
            let expect = UnassignedInteger::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>::new(
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

    pub fn native(&self) -> Witness<N> {
        self.native
    }

    pub fn big(&self) -> Value<BigUint> {
        self.big.clone()
    }

    pub fn max(&self) -> BigUint {
        // TODO: consider caching
        compose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&self.max_vals)
    }

    pub fn value(&self) -> Value<W> {
        // TODO: 'utils::compose' can be faster
        self.big.clone().map(|a| big_to_fe(&a))
    }
}

impl<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>
    From<BigUint> for ConstantInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>
{
    fn from(big: BigUint) -> Self {
        let native: N = big_to_fe(&big);
        let limbs_big = decompose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&big);
        let limbs: [N; NUMBER_OF_LIMBS] = limbs_big
            .iter()
            .map(|e| big_to_fe_unsafe(e))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        #[cfg(feature = "sanity-check")]
        {
            use circuitry::utils::compose_into;
            let expect = compose_into::<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>(&limbs);
            assert_eq!(expect, *e);
        }

        Self {
            big,
            limbs,
            limbs_big,
            native,
            _marker: PhantomData,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ConstantInteger<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
> {
    pub(crate) limbs: [N; NUMBER_OF_LIMBS],
    pub(crate) limbs_big: [BigUint; NUMBER_OF_LIMBS],
    pub(crate) native: N,
    pub(crate) big: BigUint,
    _marker: PhantomData<W>,
}
impl<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>
    ConstantInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>
{
    pub fn from_fe(e: &W) -> Self {
        let big = fe_to_big(e);
        big.into()
    }

    pub(crate) fn big(&self) -> BigUint {
        self.big.clone()
    }

    pub(crate) fn native(&self) -> N {
        self.native
    }

    pub(crate) fn limbs(&self) -> &[N; NUMBER_OF_LIMBS] {
        &self.limbs
    }

    pub(crate) fn limbs_big(&self) -> &[BigUint; NUMBER_OF_LIMBS] {
        &self.limbs_big
    }

    pub fn value(&self) -> W {
        big_to_fe(&self.big)
    }
}
