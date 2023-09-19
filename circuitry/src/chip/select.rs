use ff::PrimeField;

use crate::{
    enforcement::Selection,
    witness::{Composable, Witness},
};

use super::Chip;

pub trait SelectChip<F: PrimeField + Ord>: Chip<Selection<F>, F> {
    fn select(&mut self, cond: &Witness<F>, w0: &Witness<F>, w1: &Witness<F>) -> Witness<F> {
        let selected = w0
            .value()
            .zip(w1.value())
            .zip(cond.value())
            .map(|((w0, w1), cond)| {
                if cond == F::one() {
                    w0
                } else {
                    #[cfg(feature = "prover-sanity")]
                    {
                        assert_eq!(cond, F::zero());
                    }
                    w1
                }
            });
        let selected = self.new_witness(selected);
        self.new_op(Selection {
            cond: *cond,
            w0: *w0,
            w1: *w1,
            selected,
        });
        selected
    }
}
