use crate::chip::IntegerChip;
use crate::integer::Integer;
use circuitry::chip::first_degree::FirstDegreeChip;
use circuitry::chip::second_degree::SecondDegreeChip;
use circuitry::witness::Scaled;
use ff::PrimeField;
use num_bigint::BigUint;

impl<
        W: PrimeField,
        N: PrimeField + Ord,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const NUMBER_OF_SUBLIMBS: usize,
        const SUBLIMB_SIZE: usize,
    > IntegerChip<W, N, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>
{
    pub fn assert_not_zero<Stack: SecondDegreeChip<N> + FirstDegreeChip<N>>(
        &self,
        stack: &mut Stack,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        // unimplemented!();
        let w0 = self.reduce(stack, w0);
        // Sanity check.
        // This algorithm requires that wrong modulus * 2 <= native modulus * 2 ^
        // bit_len_limb.
        #[cfg(feature = "synth-sanity")]
        {
            let two_pow_limb_bits_minus_1 =
                BigUint::from(2u64).pow((LIMB_SIZE - 1).try_into().unwrap());
            assert!(
                self.rns.wrong_modulus.clone()
                    <= self.rns.native_modulus.clone() * two_pow_limb_bits_minus_1
            );
        }

        let terms: Vec<Scaled<N>> = w0
            .limbs
            .iter()
            .zip(self.rns.left_shifters.iter())
            .map(|(limb, base)| Scaled::new(limb, *base))
            .collect::<Vec<Scaled<N>>>();
        let native = &stack.compose(&terms[..], N::ZERO);

        // r = 0 <-> r % 2 ^ 64 = 0 /\ r % native_modulus = 0
        // r <> 0 <-> r % 2 ^ 64 <> 0 \/ r % native_modulus <> 0
        // r <> 0 <-> invert(r.limb(0)) \/ invert(r.native())
        let cond_zero_0 = stack.is_zero(&w0.limbs[0]);
        let cond_zero_1 = stack.is_zero(native);
        // one of them might be succeeded, i.e. cond_zero_0 * cond_zero_1 = 0
        let must_be_zero = stack.mul(&cond_zero_0, &cond_zero_1);
        stack.assert_zero(&must_be_zero);
        // Similar to 0,
        // r = wrong_modulus <-> r % 2 ^ 64 = wrong_modulus % 2 ^ 64 /\ r %
        // native_modulus = wrong_modulus % native_modulus r <> p <->
        // invert(r.limb(0) - wrong_modulus[0]) \/ invert(r.native() -
        // wrong_modulus.native())
        let limb_dif = stack.add_constant(&w0.limbs[0], -self.rns.wrong_modulus_limbs[0]);
        let native_dif = stack.add_constant(native, -self.rns.wrong_modulus_in_native_modulus);
        let cond_wrong_0 = stack.is_zero(&limb_dif);
        let cond_wrong_1 = stack.is_zero(&native_dif);
        let must_be_zero = stack.mul(&cond_wrong_0, &cond_wrong_1);
        stack.assert_zero(&must_be_zero);
    }
}
