use crate::circuitry::witness::{Composable, Scaled, Witness};
use ff::PrimeField;

use super::Chip;

pub trait FirstDegreeChip<F: PrimeField + Ord>:
    Chip<crate::circuitry::enforcement::FirstDegree<F>, F>
{
    fn equal_to_constant(&mut self, w0: &Witness<F>, constant: F) {
        self.zero_sum(&[w0.add()], -constant);
    }

    fn assert_zero(&mut self, w0: &Witness<F>) {
        self.equal_to_constant(w0, F::ZERO)
    }

    fn assert_one(&mut self, w0: &Witness<F>) {
        self.equal_to_constant(w0, F::ONE)
    }

    fn add(&mut self, w0: &Witness<F>, w1: &Witness<F>) -> Witness<F> {
        let u = self.new_witness(w0.value() + w1.value());
        self.zero_sum(&[w0.add(), w1.add(), u.sub()], F::ZERO);
        u
    }

    fn add_add_constant(&mut self, w0: &Witness<F>, w1: &Witness<F>, constant: F) -> Witness<F> {
        let u = self.new_witness(w0.value() + w1.value());
        let u = u.value().map(|u| u + constant);
        let u = self.new_witness(u);
        self.zero_sum(&[w0.add(), w1.add(), u.sub()], constant);
        u
    }

    fn add_constant(&mut self, w0: &Witness<F>, constant: F) -> Witness<F> {
        let u = w0.value().map(|w0| w0 + constant);
        let u = self.new_witness(u);
        self.zero_sum(&[w0.add(), u.sub()], constant);
        u
    }

    fn add_scaled(&mut self, w0: &Scaled<F>, w1: &Scaled<F>) -> Witness<F> {
        let u = self.new_witness(w0.value() + w1.value());
        self.zero_sum(&[*w0, *w1, u.sub()], F::ZERO);

        u
    }

    fn sub(&mut self, w0: &Witness<F>, w1: &Witness<F>) -> Witness<F> {
        let u = self.new_witness(w0.value() - w1.value());
        self.zero_sum(&[w0.add(), w1.sub(), u.sub()], F::ZERO);
        u
    }

    fn sub_and_add_constant(
        &mut self,
        w0: &Witness<F>,
        w1: &Witness<F>,
        constant: F,
    ) -> Witness<F> {
        let u = (w0.value() - w1.value()).map(|dif| dif + constant);
        let u = self.new_witness(u);
        self.zero_sum(&[w0.add(), w1.sub(), u.sub()], constant);
        u
    }

    fn sub_from_constant(&mut self, constant: F, w1: &Witness<F>) -> Witness<F> {
        let u = w1.value().map(|w1| constant - w1);
        let u = self.new_witness(u);
        self.zero_sum(&[w1.sub(), u.sub()], constant);

        u
    }

    fn scale(&mut self, w: Scaled<F>) -> Witness<F> {
        let u = self.new_witness(w.value());
        self.zero_sum(&[w, u.sub()], F::ZERO);
        u
    }

    fn zero_sum(&mut self, terms: &[Scaled<F>], constant: F) {
        let terms: Vec<Scaled<F>> = terms.iter().filter(|e| !e.is_empty()).cloned().collect();

        assert!(!terms.is_empty());

        #[cfg(feature = "prover-sanity")]
        {
            let result = Scaled::sum(&terms[..], constant);
            result.map(|must_be_zero| {
                assert_eq!(must_be_zero, F::ZERO);
            });
        }

        let composition = crate::circuitry::enforcement::FirstDegree::new(terms, constant);
        self.new_op(composition);
    }

    fn compose(&mut self, terms: &[Scaled<F>], constant: F) -> Witness<F> {
        let mut terms: Vec<Scaled<F>> = terms.iter().filter(|e| !e.is_empty()).cloned().collect();
        assert!(!terms.is_empty());
        let result = Scaled::sum(&terms[..], constant);
        let result = self.new_witness(result).sub();
        terms.push(result);
        let composition = crate::circuitry::enforcement::FirstDegree::new_no_range(terms, constant);
        self.new_op(composition);
        result.witness
    }
}
