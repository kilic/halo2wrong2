use std::fmt::Debug;

use ff::PrimeField;
use halo2::circuit::Value;
use num_bigint::BigUint;

use crate::utils::{decompose_into, fe_to_big};

pub trait Composable<F: PrimeField>: Sized {
    type Scaled: Composable<F>;

    fn value(&self) -> Value<F>;

    fn scale(&self, factor: F) -> Self::Scaled;

    fn sum(terms: &[Self], constant: F) -> Value<F> {
        terms.iter().fold(Value::known(constant), |acc, term| {
            acc.zip(term.value()).map(|(acc, coeff)| acc + coeff)
        })
    }

    fn as_term(&self) -> Term<F>;
}

#[derive(Clone, Copy)]
pub struct Witness<F: PrimeField> {
    pub(crate) id: Option<u32>,
    pub(crate) value: Value<F>,
    // pub(crate) range: Option<usize>,
}

impl<F: PrimeField> Debug for Witness<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug = f.debug_struct("Witness");
        debug.field("id", &self.id);
        // debug.field("range", &self.range);

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
    type Scaled = Scaled<F>;

    fn value(&self) -> Value<F> {
        self.value
    }

    fn scale(&self, factor: F) -> Self::Scaled {
        self * factor
    }

    fn as_term(&self) -> Term<F> {
        self.into()
    }
}

impl<F: PrimeField> Composable<F> for Scaled<F> {
    type Scaled = Self;

    fn value(&self) -> Value<F> {
        self.witness.value().map(|value| value * self.factor)
    }

    fn scale(&self, factor: F) -> Self::Scaled {
        self * factor
    }

    fn as_term(&self) -> Term<F> {
        self.into()
    }
}

impl<F: PrimeField> Composable<F> for SecondDegreeScaled<F> {
    type Scaled = Self;

    fn value(&self) -> Value<F> {
        self.w0
            .value()
            .zip(self.w1.value())
            .map(|(w0, w1)| w0 * w1 * self.factor)
    }

    fn scale(&self, factor: F) -> Self::Scaled {
        self * factor
    }

    fn as_term(&self) -> Term<F> {
        self.into()
    }
}

impl<F: PrimeField> Composable<F> for Term<F> {
    type Scaled = Self;

    fn value(&self) -> Value<F> {
        match self {
            Self::First(e) => e.value(),
            Self::Second(e) => e.value(),
            Self::Zero => Value::known(F::ZERO),
        }
    }

    fn scale(&self, factor: F) -> Self::Scaled {
        match self {
            Self::First(e) => e.scale(factor).into(),
            Self::Second(e) => e.scale(factor).into(),
            Self::Zero => self.clone(),
        }
    }

    fn as_term(&self) -> Term<F> {
        self.clone()
    }
}

impl<F: PrimeField> Witness<F> {
    pub fn new(id: u32, value: Value<F>) -> Self {
        Witness {
            id: Some(id),
            value,
            // range: None,
        }
    }

    pub fn new_in_range(id: u32, value: Value<F>, _bit_size: usize) -> Self {
        Witness {
            id: Some(id),
            value,
            // range: Some(bit_size),
        }
    }

    pub fn tmp(value: Value<F>) -> Self {
        Witness {
            id: None,
            value,
            // range: None,
        }
    }

    pub fn big(&self) -> Value<BigUint> {
        self.value().map(|value| fe_to_big(&value))
    }

    pub fn id(&self) -> Option<u32> {
        self.id
    }

    pub fn dummy() -> Self {
        Self::tmp(Value::known(F::ZERO))
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

    pub fn decompose(&self, number_of_limbs: usize, limb_size: usize) -> Value<Vec<F>> {
        self.value()
            .map(|value| decompose_into(&value, number_of_limbs, limb_size))
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
            factor: F::ZERO,
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.factor == F::ZERO
    }

    pub fn mul(witness: &Witness<F>) -> Self {
        Self::new(witness, F::ZERO)
    }

    pub fn add(witness: &Witness<F>) -> Self {
        Self::new(witness, F::ONE)
    }

    pub fn sub(witness: &Witness<F>) -> Self {
        Self::new(witness, -F::ONE)
    }

    pub fn result(witness: &Witness<F>) -> Self {
        Self::sub(witness)
    }

    pub fn neg(&self) -> Self {
        Self::new(&self.witness, -self.factor)
    }
}

impl<F: PrimeField> SecondDegreeScaled<F> {
    pub(crate) fn is_empty(&self) -> bool {
        self.factor == F::ZERO
    }
    pub fn new(w0: &Witness<F>, w1: &Witness<F>, factor: F) -> Self {
        Self {
            w0: *w0,
            w1: *w1,
            factor,
        }
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
}

impl<F: PrimeField> From<Witness<F>> for Scaled<F> {
    fn from(e: Witness<F>) -> Self {
        Self {
            witness: e,
            factor: F::ONE,
        }
    }
}

impl<F: PrimeField> From<&Witness<F>> for Scaled<F> {
    fn from(e: &Witness<F>) -> Self {
        Self {
            witness: *e,
            factor: F::ONE,
        }
    }
}

impl<F: PrimeField> From<Witness<F>> for Term<F> {
    fn from(e: Witness<F>) -> Self {
        Scaled {
            witness: e,
            factor: F::ONE,
        }
        .into()
    }
}

impl<F: PrimeField> From<&Witness<F>> for Term<F> {
    fn from(e: &Witness<F>) -> Self {
        Scaled {
            witness: *e,
            factor: F::ONE,
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
        SecondDegreeScaled::new(&self, &rhs, F::ONE)
    }
}

impl<F: PrimeField> std::ops::Mul<&Witness<F>> for Witness<F> {
    type Output = SecondDegreeScaled<F>;
    fn mul(self, rhs: &Self) -> Self::Output {
        SecondDegreeScaled::new(&self, rhs, F::ONE)
    }
}

impl<F: PrimeField> std::ops::Mul for &Witness<F> {
    type Output = SecondDegreeScaled<F>;
    fn mul(self, rhs: &Witness<F>) -> Self::Output {
        SecondDegreeScaled::new(self, rhs, F::ONE)
    }
}

impl<F: PrimeField> std::ops::Mul<Witness<F>> for &Witness<F> {
    type Output = SecondDegreeScaled<F>;
    fn mul(self, rhs: Witness<F>) -> Self::Output {
        SecondDegreeScaled::new(self, &rhs, F::ONE)
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

impl<F: PrimeField> std::ops::Mul<&Scaled<F>> for Witness<F> {
    type Output = SecondDegreeScaled<F>;
    fn mul(self, rhs: &Scaled<F>) -> Self::Output {
        SecondDegreeScaled::new(&self, &rhs.witness, rhs.factor)
    }
}

impl<F: PrimeField> std::ops::Mul<Scaled<F>> for Witness<F> {
    type Output = SecondDegreeScaled<F>;
    fn mul(self, rhs: Scaled<F>) -> Self::Output {
        SecondDegreeScaled::new(&self, &rhs.witness, rhs.factor)
    }
}

impl<F: PrimeField> std::ops::Mul<F> for Scaled<F> {
    type Output = Self;
    fn mul(self, rhs: F) -> Self::Output {
        Scaled::new(&self.witness, rhs * self.factor)
    }
}

impl<F: PrimeField> std::ops::Mul<F> for &Scaled<F> {
    type Output = Scaled<F>;
    fn mul(self, rhs: F) -> Self::Output {
        Scaled::new(&self.witness, rhs * self.factor)
    }
}

impl<F: PrimeField> std::ops::Mul<&F> for &Scaled<F> {
    type Output = Scaled<F>;
    fn mul(self, rhs: &F) -> Self::Output {
        Scaled::new(&self.witness, *rhs * self.factor)
    }
}

impl<F: PrimeField> std::ops::Mul<&F> for Scaled<F> {
    type Output = Self;
    fn mul(self, rhs: &F) -> Self::Output {
        Scaled::new(&self.witness, *rhs * self.factor)
    }
}

impl<F: PrimeField> std::ops::Mul<&Witness<F>> for Scaled<F> {
    type Output = SecondDegreeScaled<F>;
    fn mul(self, rhs: &Witness<F>) -> Self::Output {
        SecondDegreeScaled::new(&self.witness, rhs, self.factor)
    }
}

impl<F: PrimeField> std::ops::Mul<Witness<F>> for Scaled<F> {
    type Output = SecondDegreeScaled<F>;
    fn mul(self, rhs: Witness<F>) -> Self::Output {
        SecondDegreeScaled::new(&self.witness, &rhs, self.factor)
    }
}

impl<F: PrimeField> std::ops::Mul<F> for SecondDegreeScaled<F> {
    type Output = Self;
    fn mul(self, rhs: F) -> Self::Output {
        SecondDegreeScaled::new(&self.w0, &self.w1, rhs * self.factor)
    }
}

impl<F: PrimeField> std::ops::Mul<F> for &SecondDegreeScaled<F> {
    type Output = SecondDegreeScaled<F>;
    fn mul(self, rhs: F) -> Self::Output {
        SecondDegreeScaled::new(&self.w0, &self.w1, rhs * self.factor)
    }
}

impl<F: PrimeField> std::ops::Mul<&F> for &SecondDegreeScaled<F> {
    type Output = SecondDegreeScaled<F>;
    fn mul(self, rhs: &F) -> Self::Output {
        SecondDegreeScaled::new(&self.w0, &self.w1, *rhs * self.factor)
    }
}

impl<F: PrimeField> std::ops::Mul<&F> for SecondDegreeScaled<F> {
    type Output = Self;
    fn mul(self, rhs: &F) -> Self::Output {
        SecondDegreeScaled::new(&self.w0, &self.w1, *rhs * self.factor)
    }
}
