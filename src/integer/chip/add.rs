use crate::circuitry::chip::first_degree::FirstDegreeChip;
use crate::circuitry::stack::Stack;
use crate::circuitry::witness::{Composable, Scaled, Witness};
use crate::integer::chip::IntegerChip;
use crate::integer::{ConstantInteger, Integer};
use crate::utils::compose;
use ff::PrimeField;
use num_bigint::BigUint;

impl<W: PrimeField, N: PrimeField + Ord> IntegerChip<W, N> {
    pub fn double(&self, stack: &mut Stack<N>, a: &Integer<W, N>) -> Integer<W, N> {
        self.add(stack, a, a)
    }

    pub fn add(&self, stack: &mut Stack<N>, a: &Integer<W, N>, b: &Integer<W, N>) -> Integer<W, N> {
        #[cfg(feature = "synth-sanity")]
        {
            let c = a.max() + b.max();
            assert!(self.rns._max_unreduced_value > c);
        }

        let limbs = a
            .limbs()
            .iter()
            .zip(b.limbs().iter())
            .map(|(a, b)| stack.add(a, b))
            .collect::<Vec<Witness<N>>>();

        let max_vals = a
            .max_vals()
            .iter()
            .zip(b.max_vals().iter())
            .map(|(a, b)| a + b)
            .collect::<Vec<BigUint>>();

        let native = stack.add(a.native(), b.native());
        Integer::new(
            &limbs,
            &max_vals,
            a.big() + b.big(),
            native,
            self.rns.limb_size,
        )
    }

    pub fn add_constant(
        &self,
        stack: &mut Stack<N>,
        a: &Integer<W, N>,
        constant: &ConstantInteger<W, N>,
    ) -> Integer<W, N> {
        #[cfg(feature = "synth-sanity")]
        {
            let c = a.max() + constant.big();
            assert!(self.rns._max_unreduced_value > c);
        }

        let limbs = a
            .limbs()
            .iter()
            .zip(constant.limbs().iter())
            .map(|(a, b)| stack.add_constant(a, *b))
            .collect::<Vec<Witness<N>>>();

        let max_vals = a
            .max_vals()
            .iter()
            .zip(constant.big_limbs().iter())
            .map(|(a, b)| a + b)
            .collect::<Vec<BigUint>>();

        let native = stack.add_constant(a.native(), constant.native());

        Integer::new(
            &limbs,
            &max_vals,
            a.big().as_ref().map(|a| a + constant.big()),
            native,
            self.rns.limb_size,
        )
    }

    pub fn sub(&self, stack: &mut Stack<N>, a: &Integer<W, N>, b: &Integer<W, N>) -> Integer<W, N> {
        #[cfg(feature = "synth-sanity")]
        {
            let c = a.max() + b.max();
            assert!(self.rns._max_unreduced_value > c, "pre aux");
        }

        let (aux_witness, aux_big, aux_nat) = self.get_sub_aux(b.max_vals());

        #[cfg(feature = "synth-sanity")]
        {
            let c = a.max() + compose(&aux_big, self.rns.limb_size);
            assert!(self.rns._max_unreduced_value > c, "post aux");
        }

        let limbs = a
            .limbs()
            .iter()
            .zip(b.limbs().iter())
            .zip(aux_witness)
            .map(|((a, b), aux)| stack.sub_and_add_constant(a, b, aux))
            .collect::<Vec<Witness<N>>>();

        let max_vals = a
            .max_vals()
            .iter()
            .zip(aux_big.iter())
            .map(|(a_limb, aux)| a_limb + aux)
            .collect::<Vec<BigUint>>();

        let native = stack.sub_and_add_constant(a.native(), b.native(), aux_nat);

        let big = a
            .big()
            .zip(b.big())
            .map(|(a, b)| ((a + compose(&aux_big, self.rns.limb_size)) - b));

        Integer::new(&limbs, &max_vals, big, native, self.rns.limb_size)
    }

    pub fn neg(&self, stack: &mut Stack<N>, a: &Integer<W, N>) -> Integer<W, N> {
        #[cfg(feature = "synth-sanity")]
        {
            let c = a.max();
            assert!(self.rns._max_unreduced_value > c, "pre aux");
        }

        let (aux_witness, aux_big, aux_nat) = self.get_sub_aux(a.max_vals());

        #[cfg(feature = "synth-sanity")]
        {
            let c = a.max() + compose(&aux_big, self.rns.limb_size);
            assert!(self.rns._max_unreduced_value > c, "post aux");
        }

        let limbs = a
            .limbs()
            .iter()
            .zip(aux_witness)
            .map(|(a, aux)| stack.sub_from_constant(aux, a))
            .collect::<Vec<Witness<N>>>();

        let max_vals = a
            .max_vals()
            .iter()
            .zip(aux_big.iter())
            .map(|(a_limb, aux)| a_limb + aux)
            .collect::<Vec<BigUint>>();

        let native = stack.sub_from_constant(aux_nat, a.native());

        let big = a
            .big()
            .map(|a| ((compose(&aux_big, self.rns.limb_size)) - a));

        Integer::new(&limbs, &max_vals, big, native, self.rns.limb_size)
    }

    pub fn mul2(&self, stack: &mut Stack<N>, a: &Integer<W, N>) -> Integer<W, N> {
        #[cfg(feature = "synth-sanity")]
        {
            let c = a.max() * 2usize;
            assert!(self.rns._max_unreduced_value > c);
        }

        let limbs = a
            .limbs()
            .iter()
            .map(|limb| stack.scale(Scaled::new(limb, N::from(2))))
            .collect::<Vec<Witness<N>>>();

        let max_vals = a
            .max_vals()
            .iter()
            .map(|max_val| max_val * 2usize)
            .collect::<Vec<BigUint>>();

        let native = stack.scale(a.native().scale(N::from(2)));
        Integer::new(
            &limbs,
            &max_vals,
            a.big().map(|a| a * 2usize),
            native,
            self.rns.limb_size,
        )
    }

    pub fn mul3(&self, stack: &mut Stack<N>, a: &Integer<W, N>) -> Integer<W, N> {
        // #[cfg(feature = "synth-sanity")]
        // {
        // let c = a.max() * 3usize;
        // assert!(self.rns._max_unreduced_value > c);
        // }

        let limbs = a
            .limbs()
            .iter()
            .map(|limb| stack.scale(Scaled::new(limb, N::from(3))))
            .collect::<Vec<Witness<N>>>();

        let max_vals = a
            .max_vals()
            .iter()
            .map(|max_val| max_val * 3usize)
            .collect::<Vec<BigUint>>();

        let native = stack.scale(a.native().scale(N::from(3)));
        Integer::new(
            &limbs,
            &max_vals,
            a.big().map(|a| (a * 3usize)),
            native,
            self.rns.limb_size,
        )
    }
}
