use crate::chip::IntegerChip;
use crate::integer::{ConstantInteger, Integer};
use circuitry::chip::first_degree::FirstDegreeChip;
use circuitry::stack::Stack;
use circuitry::utils::compose;
use circuitry::witness::{Composable, Scaled, Witness};
use ff::PrimeField;
use num_bigint::BigUint;

impl<
        W: PrimeField,
        N: PrimeField + Ord,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    > IntegerChip<W, N, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>
{
    pub fn add(
        &self,
        stack: &mut Stack<N>,
        a: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        b: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
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
            .collect::<Vec<Witness<N>>>()
            .try_into()
            .unwrap();

        let max_vals = a
            .max_vals()
            .iter()
            .zip(b.max_vals().iter())
            .map(|(a, b)| a + b)
            .collect::<Vec<BigUint>>()
            .try_into()
            .unwrap();

        let native = stack.add(a.native(), b.native());
        Integer::new(&limbs, &max_vals, a.big() + b.big(), native)
    }

    pub fn add_constant(
        &self,
        stack: &mut Stack<N>,
        a: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        constant: &ConstantInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
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
            .collect::<Vec<Witness<N>>>()
            .try_into()
            .unwrap();

        let max_vals = a
            .max_vals()
            .iter()
            .zip(constant.big_limbs().iter())
            .map(|(a, b)| a + b)
            .collect::<Vec<BigUint>>()
            .try_into()
            .unwrap();

        let native = stack.add_constant(a.native(), constant.native());

        Integer::new(
            &limbs,
            &max_vals,
            a.big().as_ref().map(|a| a + constant.big()),
            native,
        )
    }

    pub fn sub(
        &self,
        stack: &mut Stack<N>,
        a: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        b: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        #[cfg(feature = "synth-sanity")]
        {
            let c = a.max() + b.max();
            assert!(self.rns._max_unreduced_value > c, "pre aux");
        }

        let (aux_witness, aux_big, aux_nat) = self.get_sub_aux(b.max_vals());

        #[cfg(feature = "synth-sanity")]
        {
            let c = a.max() + compose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&aux_big);
            assert!(self.rns._max_unreduced_value > c, "post aux");
        }

        let limbs = a
            .limbs()
            .iter()
            .zip(b.limbs().iter())
            .zip(aux_witness)
            .map(|((a, b), aux)| stack.sub_and_add_constant(a, b, aux))
            .collect::<Vec<Witness<N>>>()
            .try_into()
            .unwrap();

        let max_vals = a
            .max_vals()
            .iter()
            .zip(aux_big.iter())
            .map(|(a_limb, aux)| a_limb + aux)
            .collect::<Vec<BigUint>>()
            .try_into()
            .unwrap();

        let native = stack.sub_and_add_constant(a.native(), b.native(), aux_nat);

        let big = a
            .big()
            .zip(b.big())
            .map(|(a, b)| ((a + compose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&aux_big)) - b));

        Integer::new(&limbs, &max_vals, big, native)
    }

    pub fn neg(
        &self,
        stack: &mut Stack<N>,
        a: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        #[cfg(feature = "synth-sanity")]
        {
            let c = a.max();
            assert!(self.rns._max_unreduced_value > c, "pre aux");
        }

        let (aux_witness, aux_big, aux_nat) = self.get_sub_aux(a.max_vals());

        #[cfg(feature = "synth-sanity")]
        {
            let c = a.max() + compose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&aux_big);
            assert!(self.rns._max_unreduced_value > c, "post aux");
        }

        let limbs = a
            .limbs()
            .iter()
            .zip(aux_witness)
            .map(|(a, aux)| stack.sub_from_constant(aux, a))
            .collect::<Vec<Witness<N>>>()
            .try_into()
            .unwrap();

        let max_vals = a
            .max_vals()
            .iter()
            .zip(aux_big.iter())
            .map(|(a_limb, aux)| a_limb + aux)
            .collect::<Vec<BigUint>>()
            .try_into()
            .unwrap();

        let native = stack.sub_from_constant(aux_nat, a.native());

        let big = a
            .big()
            .map(|a| ((compose::<NUMBER_OF_LIMBS, LIMB_SIZE>(&aux_big)) - a));

        Integer::new(&limbs, &max_vals, big, native)
    }

    pub fn mul2(
        &self,
        stack: &mut Stack<N>,
        a: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        #[cfg(feature = "synth-sanity")]
        {
            let c = a.max() * 2usize;
            assert!(self.rns._max_unreduced_value > c);
        }

        let limbs = a
            .limbs()
            .iter()
            .map(|limb| stack.scale(Scaled::new(limb, N::from(2))))
            .collect::<Vec<Witness<N>>>()
            .try_into()
            .unwrap();

        let max_vals = a
            .max_vals()
            .iter()
            .map(|max_val| max_val * 2usize)
            .collect::<Vec<BigUint>>()
            .try_into()
            .unwrap();

        let native = stack.scale(a.native().scale(N::from(2)));
        Integer::new(&limbs, &max_vals, a.big().map(|a| a * 2usize), native)
    }

    pub fn mul3(
        &self,
        stack: &mut Stack<N>,
        a: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        // #[cfg(feature = "synth-sanity")]
        // {
        // let c = a.max() * 3usize;
        // assert!(self.rns._max_unreduced_value > c);
        // }

        let limbs = a
            .limbs()
            .iter()
            .map(|limb| stack.scale(Scaled::new(limb, N::from(3))))
            .collect::<Vec<Witness<N>>>()
            .try_into()
            .unwrap();

        let max_vals = a
            .max_vals()
            .iter()
            .map(|max_val| max_val * 3usize)
            .collect::<Vec<BigUint>>()
            .try_into()
            .unwrap();

        let native = stack.scale(a.native().scale(N::from(3)));
        Integer::new(&limbs, &max_vals, a.big().map(|a| (a * 3usize)), native)
    }
}
