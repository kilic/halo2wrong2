use ff::PrimeField;

use crate::witness::{Scaled, Term, Witness};

#[derive(Clone, Debug)]
pub enum MemoryOperation<F: PrimeField, const W: usize> {
    Write {
        tag: F,
        address: F,
        values: [Witness<F>; W],
    },
    Read {
        tag: F,
        address_base: F,
        address_fraction: Witness<F>,
        values: [Witness<F>; W],
    },
}

#[derive(Debug, Clone)]
pub struct FirstDegreeComposition<F: PrimeField> {
    pub(crate) terms: Vec<Scaled<F>>,
    pub(crate) constant: F,
    pub(crate) is_range_decomposition: bool,
}

#[derive(Debug, Clone)]
pub struct SecondDegreeComposition<F: PrimeField> {
    pub(crate) terms: Vec<Term<F>>,
    pub(crate) constant: F,
}

impl<F: PrimeField> FirstDegreeComposition<F> {
    pub fn new(terms: Vec<Scaled<F>>, constant: F) -> Self {
        let is_range_decomposition = Self::_is_range_demoposition(&terms);
        FirstDegreeComposition {
            terms,
            constant,
            is_range_decomposition,
        }
    }

    pub fn new_no_range(terms: Vec<Scaled<F>>, constant: F) -> Self {
        FirstDegreeComposition {
            terms,
            constant,
            is_range_decomposition: false,
        }
    }

    pub fn is_simple(&self) -> bool {
        self.terms.len() <= 3
    }

    fn _is_range_demoposition(terms: &[Scaled<F>]) -> bool {
        if terms.len() == 1 {
            return terms[0].witness.range.is_some();
        }
        let mut decision = true;
        for term in terms.iter().rev().skip(1) {
            decision = decision & term.witness.range.is_some()
        }
        decision
    }

    pub fn is_range_demoposition(&self) -> bool {
        // Self::_is_range_demoposition(&self.terms)
        self.is_range_decomposition
    }

    pub fn len(&self) -> usize {
        self.terms.len()
    }

    pub fn has_constant(&self) -> bool {
        self.constant != F::zero()
    }
}

impl<F: PrimeField> SecondDegreeComposition<F> {
    pub fn new(terms: Vec<Term<F>>, constant: F) -> Self {
        SecondDegreeComposition { terms, constant }
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
