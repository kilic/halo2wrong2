use std::fmt::Debug;

use crate::halo2::circuit::Value;
use ff::PrimeField;

use crate::utils::{decompose_into, decompose_into_dyn, fe_to_big};

pub trait Composable<F: PrimeField>: Sized {
    fn value(&self) -> Value<F>;

    fn compose(terms: &[Self], constant: F) -> Value<F> {
        terms.iter().fold(Value::known(constant), |acc, term| {
            acc.zip(term.value()).map(|(acc, coeff)| acc + coeff)
        })
    }
}

#[derive(Clone, Copy)]
pub struct Witness<F: PrimeField> {
    pub(crate) id: Option<u32>,
    pub(crate) value: Value<F>,
    pub(crate) range: Option<usize>,
}

impl<F: PrimeField> Debug for Witness<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug = f.debug_struct("Witness");
        debug.field("id", &self.id);
        debug.field("range", &self.range);

        self.value().map(|value| {
            let bit_size = fe_to_big(&value).bits();
            debug.field("bit_size", &bit_size);
            debug.field("value", &value);
        });

        debug.finish()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Scaled<F: PrimeField> {
    pub(crate) witness: Witness<F>,
    pub(crate) factor: F,
}

#[derive(Debug, Clone, Copy)]
pub struct SecondDegreeScaled<F: PrimeField> {
    pub(crate) w0: Witness<F>,
    pub(crate) w1: Witness<F>,
    pub(crate) factor: F,
}

#[derive(Debug, Clone)]
pub enum Term<F: PrimeField> {
    First(Scaled<F>),
    Second(SecondDegreeScaled<F>),

    Zero,
}

impl<F: PrimeField> Composable<F> for Witness<F> {
    fn value(&self) -> Value<F> {
        self.value
    }
}

impl<F: PrimeField> Composable<F> for Scaled<F> {
    fn value(&self) -> Value<F> {
        self.witness.value().map(|value| value * self.factor)
    }
}

impl<F: PrimeField> Composable<F> for SecondDegreeScaled<F> {
    fn value(&self) -> Value<F> {
        self.w0
            .value()
            .zip(self.w1.value())
            .map(|(w0, w1)| w0 * w1 * self.factor)
    }
}

impl<F: PrimeField> Composable<F> for Term<F> {
    fn value(&self) -> Value<F> {
        match self {
            Self::First(e) => e.value(),
            Self::Second(e) => e.value(),
            Self::Zero => Value::known(F::zero()),
        }
    }
}

impl<F: PrimeField> Witness<F> {
    pub fn new(id: u32, value: Value<F>) -> Self {
        Witness {
            id: Some(id),
            value,
            range: None,
        }
    }

    pub fn new_in_range(id: u32, value: Value<F>, bit_size: usize) -> Self {
        Witness {
            id: Some(id),
            value,
            range: Some(bit_size),
        }
    }

    pub fn tmp(value: Value<F>) -> Self {
        Witness {
            id: None,
            value,
            range: None,
        }
    }

    pub fn id(&self) -> Option<u32> {
        self.id
    }

    pub fn dummy() -> Self {
        Self::tmp(Value::known(F::zero()))
    }

    pub fn mul(&self) -> Scaled<F> {
        Scaled::mul(self)
    }

    pub fn add(&self) -> Scaled<F> {
        Scaled::add(self)
    }

    pub fn sub(&self) -> Scaled<F> {
        Scaled::sub(self)
    }

    pub fn scale(&self, scale: F) -> Scaled<F> {
        Scaled::new(self, scale)
    }

    pub fn decompose<const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>(
        &self,
    ) -> Value<[F; NUMBER_OF_LIMBS]> {
        self.value()
            .map(|value| decompose_into::<F, F, NUMBER_OF_LIMBS, LIMB_SIZE>(&value))
    }

    pub fn decompose_generic(&self, number_of_limbs: usize, limb_size: usize) -> Value<Vec<F>> {
        self.value()
            .map(|value| decompose_into_dyn(&value, number_of_limbs, limb_size))
    }
}

impl<F: PrimeField> Scaled<F> {
    pub fn new(witness: &Witness<F>, factor: F) -> Self {
        Self {
            witness: *witness,
            factor,
        }
    }

    pub fn tmp(value: Value<F>, scale: F) -> Self {
        Self::new(&Witness::tmp(value), scale)
    }

    pub fn dummy() -> Self {
        Scaled {
            witness: Witness::dummy(),
            factor: F::zero(),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.factor == F::zero()
    }

    pub fn mul(witness: &Witness<F>) -> Self {
        Self::new(witness, F::zero())
    }

    pub fn add(witness: &Witness<F>) -> Self {
        Self::new(witness, F::one())
    }

    pub fn sub(witness: &Witness<F>) -> Self {
        Self::new(witness, -F::one())
    }

    pub fn result(witness: &Witness<F>) -> Self {
        Self::sub(witness)
    }

    pub fn neg(&self) -> Self {
        Self::new(&self.witness, -self.factor)
    }

    pub fn scale(&self, scale: F) -> Self {
        Scaled::new(&self.witness, self.factor * scale)
    }
}

impl<F: PrimeField> SecondDegreeScaled<F> {
    pub(crate) fn is_empty(&self) -> bool {
        self.factor == F::zero()
    }
    pub fn new(w0: &Witness<F>, w1: &Witness<F>, factor: F) -> Self {
        Self {
            w0: *w0,
            w1: *w1,
            factor,
        }
    }

    pub fn scale(&self, scale: F) -> Self {
        SecondDegreeScaled::new(&self.w0, &self.w1, self.factor * scale)
    }
}

impl<F: PrimeField> Term<F> {
    pub(crate) fn is_empty(&self) -> bool {
        match self {
            Self::First(e) => e.is_empty(),
            Self::Second(e) => e.is_empty(),
            Self::Zero => true,
        }
    }

    pub fn scale(&self, factor: F) -> Term<F> {
        match self {
            Self::First(e) => e.scale(factor).into(),
            Self::Second(e) => e.scale(factor).into(),
            Self::Zero => Self::Zero,
        }
    }
}

impl<F: PrimeField> From<Witness<F>> for Scaled<F> {
    fn from(e: Witness<F>) -> Self {
        Self {
            witness: e,
            factor: F::one(),
        }
    }
}

impl<F: PrimeField> From<&Witness<F>> for Scaled<F> {
    fn from(e: &Witness<F>) -> Self {
        Self {
            witness: *e,
            factor: F::one(),
        }
    }
}

impl<F: PrimeField> From<Witness<F>> for Term<F> {
    fn from(e: Witness<F>) -> Self {
        Scaled {
            witness: e,
            factor: F::one(),
        }
        .into()
    }
}

impl<F: PrimeField> From<&Witness<F>> for Term<F> {
    fn from(e: &Witness<F>) -> Self {
        Scaled {
            witness: *e,
            factor: F::one(),
        }
        .into()
    }
}

impl<F: PrimeField> From<Scaled<F>> for Term<F> {
    fn from(e: Scaled<F>) -> Self {
        Self::First(e)
    }
}

impl<F: PrimeField> From<SecondDegreeScaled<F>> for Term<F> {
    fn from(e: SecondDegreeScaled<F>) -> Self {
        Self::Second(e)
    }
}

impl<F: PrimeField> From<&Scaled<F>> for Term<F> {
    fn from(e: &Scaled<F>) -> Self {
        Self::First(*e)
    }
}

impl<F: PrimeField> From<&SecondDegreeScaled<F>> for Term<F> {
    fn from(e: &SecondDegreeScaled<F>) -> Self {
        Self::Second(*e)
    }
}

impl<F: PrimeField> std::ops::Mul for Witness<F> {
    type Output = SecondDegreeScaled<F>;
    fn mul(self, rhs: Self) -> Self::Output {
        SecondDegreeScaled::new(&self, &rhs, F::one())
    }
}

impl<F: PrimeField> std::ops::Mul<&Witness<F>> for Witness<F> {
    type Output = SecondDegreeScaled<F>;
    fn mul(self, rhs: &Self) -> Self::Output {
        SecondDegreeScaled::new(&self, rhs, F::one())
    }
}

impl<F: PrimeField> std::ops::Mul for &Witness<F> {
    type Output = SecondDegreeScaled<F>;
    fn mul(self, rhs: &Witness<F>) -> Self::Output {
        SecondDegreeScaled::new(self, rhs, F::one())
    }
}

impl<F: PrimeField> std::ops::Mul<Witness<F>> for &Witness<F> {
    type Output = SecondDegreeScaled<F>;
    fn mul(self, rhs: Witness<F>) -> Self::Output {
        SecondDegreeScaled::new(self, &rhs, F::one())
    }
}

impl<F: PrimeField> std::ops::Mul<F> for Witness<F> {
    type Output = Scaled<F>;
    fn mul(self, rhs: F) -> Self::Output {
        Scaled::new(&self, rhs)
    }
}

impl<F: PrimeField> std::ops::Mul<F> for &Witness<F> {
    type Output = Scaled<F>;
    fn mul(self, rhs: F) -> Self::Output {
        Scaled::new(self, rhs)
    }
}

impl<F: PrimeField> std::ops::Mul<&F> for &Witness<F> {
    type Output = Scaled<F>;
    fn mul(self, rhs: &F) -> Self::Output {
        Scaled::new(self, *rhs)
    }
}

impl<F: PrimeField> std::ops::Mul<&F> for Witness<F> {
    type Output = Scaled<F>;
    fn mul(self, rhs: &F) -> Self::Output {
        Scaled::new(&self, *rhs)
    }
}
