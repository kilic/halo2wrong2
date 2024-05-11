use crate::circuitry::witness::{Scaled, Term, Witness};
use ff::PrimeField;

#[derive(Clone, Debug)]
pub enum ROM<F: PrimeField> {
    Write {
        tag: F,
        address: F,
        values: Vec<Witness<F>>,
    },
    Read {
        tag: F,
        address_base: F,
        address_fraction: Witness<F>,
        values: Vec<Witness<F>>,
    },
}

#[derive(Debug, Clone)]
pub struct FirstDegree<F: PrimeField> {
    pub(crate) terms: Vec<Scaled<F>>,
    pub(crate) constant: F,
}

#[derive(Debug, Clone)]
pub struct RangeLimbs<F: PrimeField> {
    pub(crate) limbs: Vec<Witness<F>>,
    pub(crate) composed: Witness<F>,
    pub(crate) limb_size: usize,
    pub(crate) overflow_size: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct Range<F: PrimeField> {
    pub(crate) witness: Witness<F>,
    pub(crate) size: usize,
}

pub enum RangeOp<F: PrimeField> {
    Limbs(RangeLimbs<F>),
    Single(Range<F>),
}

#[derive(Debug, Clone)]
pub struct SecondDegree<F: PrimeField> {
    pub(crate) terms: Vec<Term<F>>,
    pub(crate) constant: F,
}

impl<F: PrimeField> RangeLimbs<F> {
    pub fn new(
        composed: Witness<F>,
        limbs: &[Witness<F>],
        limb_size: usize,
        overflow_size: Option<usize>,
    ) -> Self {
        RangeLimbs {
            composed,
            limbs: limbs.to_vec(),
            limb_size,
            overflow_size,
        }
    }
}

impl<F: PrimeField> Range<F> {
    pub fn new(witness: Witness<F>, size: usize) -> Self {
        Range { witness, size }
    }
}

impl<F: PrimeField> FirstDegree<F> {
    pub fn new(terms: Vec<Scaled<F>>, constant: F) -> Self {
        FirstDegree { terms, constant }
    }

    pub fn new_no_range(terms: Vec<Scaled<F>>, constant: F) -> Self {
        FirstDegree { terms, constant }
    }

    pub fn has_constant(&self) -> bool {
        self.constant != F::ZERO
    }
}

impl<F: PrimeField> SecondDegree<F> {
    pub fn new(terms: Vec<Term<F>>, constant: F) -> Self {
        SecondDegree { terms, constant }
    }
}

#[derive(Debug, Clone)]
pub struct Selection<F: PrimeField> {
    pub(crate) cond: Witness<F>,
    pub(crate) w0: Witness<F>,
    pub(crate) w1: Witness<F>,
    pub(crate) selected: Witness<F>,
}

impl<F: PrimeField> Selection<F> {
    pub fn new(cond: Witness<F>, w0: Witness<F>, w1: Witness<F>, selected: Witness<F>) -> Self {
        Selection {
            cond,
            w0,
            w1,
            selected,
        }
    }
}

// #[derive(Clone, Debug)]
// pub enum CRT256<F: PrimeField, const NUMBER_OF_LIMBS: usize> {
//     Mul {
//         w0: [Witness<F>; NUMBER_OF_LIMBS],
//         w1: [Witness<F>; NUMBER_OF_LIMBS],
//         result: [Witness<F>; NUMBER_OF_LIMBS],
//         quotient: [Witness<F>; NUMBER_OF_LIMBS],
//         carries: [Witness<F>; NUMBER_OF_LIMBS],
//         to_sub: [Witness<F>; NUMBER_OF_LIMBS],
//     },
//     Reduce {
//         w0: [Witness<F>; NUMBER_OF_LIMBS],
//         result: [Witness<F>; NUMBER_OF_LIMBS],
//         carries: [Witness<F>; NUMBER_OF_LIMBS],
//         quotient: Witness<F>,
//     },
// }
