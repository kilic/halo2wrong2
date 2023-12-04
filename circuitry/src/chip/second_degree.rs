use crate::witness::{Composable, Term, Witness};
use ff::PrimeField;
use halo2::circuit::Value;

use super::Chip;

pub trait SecondDegreeChip<F: PrimeField + Ord>:
    Chip<crate::enforcement::SecondDegree<F>, F>
{
    fn assign_bit(&mut self, w0: Value<F>) -> Witness<F> {
        let w0 = self.new_witness(w0);
        self.assert_bit(&w0);
        w0
    }

    fn assert_bit(&mut self, w0: &Witness<F>) {
        self.zero_sum_second_degree(&[(w0 * w0).into(), w0.sub().into()], F::ZERO);
    }

    fn mul(&mut self, w0: &Witness<F>, w1: &Witness<F>) -> Witness<F> {
        let u = self.new_witness(w0.value() * w1.value());
        self.zero_sum_second_degree(&[(w0 * w1).into(), u.sub().into()], F::ZERO);
        u
    }

    fn mul_add_constant_scaled(
        &mut self,
        factor: F,
        w0: &Witness<F>,
        w1: &Witness<F>,
        constant: F,
    ) -> Witness<F> {
        let u = (w0.value() * w1.value()).map(|e| factor * e + constant);
        let u = self.new_witness(u);
        self.zero_sum_second_degree(&[(w0 * w1).scale(factor).into(), u.sub().into()], constant);
        u
    }

    fn mul_add_constant(&mut self, w0: &Witness<F>, w1: &Witness<F>, constant: F) -> Witness<F> {
        self.mul_add_constant_scaled(F::ONE, w0, w1, constant)
    }

    fn assert_not_zero(&mut self, w: &Witness<F>) {
        self.inv_incomplete(w);
    }

    // fn assert_not_equal(&mut self, w0: &Witness<F>, w1: &Witness<F>) {
    //     let u = self.sub(w0, w1);
    //     self.assert_not_zero(&u)
    // }

    fn div_incomplete(&mut self, w0: &Witness<F>, w1: &Witness<F>) -> Witness<F> {
        let u = w0
            .value()
            .zip(w1.value())
            .map(|(w0, w1)| w0 * w1.invert().expect("div: must be invertable"));

        let u = self.new_witness(u);

        self.zero_sum_second_degree(&[(u * w1).into(), w0.sub().into()], F::ZERO);
        u
    }

    fn inv_incomplete(&mut self, w: &Witness<F>) -> Witness<F> {
        let u = w
            .value()
            .map(|w| w.invert().expect("inv: must be invertable"));
        let u = self.new_witness(u);
        let one = self.get_constant(F::ONE);
        self.zero_sum_second_degree(&[(u * w).into(), one.sub().into()], F::ZERO);
        u
    }

    fn inv(&mut self, w: &Witness<F>) -> (Witness<F>, Witness<F>) {
        let (sign, inv) = w
            .value()
            .map(|w0| {
                Option::from(w0.invert())
                    .map(|inverted| (F::ZERO, inverted))
                    .unwrap_or_else(|| (F::ONE, F::ONE))
            })
            .unzip();
        let sign = self.new_witness(sign);
        let inv = self.new_witness(inv);
        self.assert_bit(&sign);
        self.zero_sum_second_degree(&[(sign * inv).into(), sign.sub().into()], F::ZERO);
        self.mul_add_constant_scaled(-F::ONE, w, &inv, F::ONE);
        (inv, sign)
    }

    fn is_zero(&mut self, w0: &Witness<F>) -> Witness<F> {
        let (_, sign) = self.inv(w0);
        sign
    }

    fn zero_sum_second_degree(&mut self, terms: &[Term<F>], constant_to_add: F) {
        let terms: Vec<Term<F>> = terms.iter().filter(|e| !e.is_empty()).cloned().collect();

        assert!(!terms.is_empty());

        #[cfg(feature = "prover-sanity")]
        {
            let result = Term::sum(&terms[..], constant_to_add);
            result.map(|must_be_zero| {
                debug_assert_eq!(must_be_zero, F::ZERO);
            });
        }

        let composition = crate::enforcement::SecondDegree::new(terms, constant_to_add);
        self.new_op(composition);
    }

    fn compose_second_degree(&mut self, terms: &[Term<F>], constant_to_add: F) -> Witness<F> {
        let mut terms: Vec<Term<F>> = terms.iter().filter(|e| !e.is_empty()).cloned().collect();
        assert!(!terms.is_empty());
        let result = Term::sum(&terms[..], constant_to_add);
        let result = self.new_witness(result).sub();
        terms.push(result.into());
        let composition = crate::enforcement::SecondDegree::new(terms, constant_to_add);
        self.new_op(composition);
        result.witness
    }
}
