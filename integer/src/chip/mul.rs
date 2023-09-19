use crate::chip::IntegerChip;
use crate::integer::{Integer, Range};
use circuitry::chip::first_degree::FirstDegreeChip;
use circuitry::chip::second_degree::SecondDegreeChip;
use circuitry::witness::{Composable, Scaled, SecondDegreeScaled, Term};
use ff::PrimeField;
use num_bigint::BigUint;
use num_traits::Zero;

impl<
        W: PrimeField,
        N: PrimeField + Ord,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const NUMBER_OF_SUBLIMBS: usize,
        const SUBLIMB_SIZE: usize,
    > IntegerChip<W, N, NUMBER_OF_LIMBS, LIMB_SIZE, NUMBER_OF_SUBLIMBS, SUBLIMB_SIZE>
{
    pub fn square<Stack: SecondDegreeChip<N> + FirstDegreeChip<N>>(
        &self,
        stack: &mut Stack,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let w0 = &self.reduce_if_gt_max_operand(stack, w0);

        // t0 = a0a0
        // t1 = 2 * a0a1
        // t2 = 2 * a0a2 + a1a1
        // t3 = 2 * a0a3 + 2 * a1a2
        // t4 = 2 * a0a4 + 2 * a1a3 + a2a2

        let (result, quotient) = self.rns.mul_witness(w0, w0, &[]);
        let result = self.range(stack, result, Range::Remainder);
        let quotient = self.range(stack, quotient, Range::MulQuotient);

        let base = self.rns.rsh(1);
        let intermediate = (0..NUMBER_OF_LIMBS)
            .map(|i| {
                (0..i / 2 + 1)
                    .map(|j| {
                        let k = i - j;
                        let base = *base * (if j == k { N::ONE } else { N::from(2) });
                        SecondDegreeScaled::new(&w0.limbs[j], &w0.limbs[k], base).into()
                    })
                    .chain(
                        quotient
                            .limbs
                            .iter()
                            .take(i + 1)
                            .zip(
                                self.rns
                                    .negative_wrong_modulus_decomposed
                                    .iter()
                                    .take(i + 1)
                                    .rev(),
                            )
                            .map(|(q, p)| (Scaled::new(q, *p * base)).into()),
                    )
                    .chain(std::iter::once_with(|| {
                        result.limbs[i].scale(base.neg()).into()
                    }))
                    .collect::<Vec<Term<_>>>()
            })
            .collect::<Vec<_>>();

        let mut carry_max = BigUint::zero();
        let max_carries = (1..=NUMBER_OF_LIMBS).map(|i| {
            let t = w0
                .max_vals
                .iter()
                .take(i)
                .zip(w0.max_vals.iter().take(i).rev())
                .map(|(w0, w1)| w0 * w1)
                .chain(
                    quotient
                        .max_vals
                        .iter()
                        .take(i)
                        .zip(
                            self.rns
                                .negative_wrong_modulus_decomposed_big
                                .iter()
                                .take(i)
                                .rev(),
                        )
                        .map(|(q, p)| q * p),
                )
                .chain(std::iter::once(carry_max.clone()))
                .sum::<BigUint>();

            assert!(t < self.rns.native_modulus, "wraps");

            carry_max = t >> LIMB_SIZE;
            carry_max.bits()
        });

        let mut carry: Term<N> = Term::Zero;
        for (terms, carry_max) in intermediate.iter().zip(max_carries) {
            let terms = terms
                .iter()
                .chain(std::iter::once(&carry.clone()))
                .cloned()
                .collect::<Vec<Term<N>>>();

            let carry_tmp_0 = &stack.compose_second_degree(&terms[..], N::ZERO);

            let carry_tmp_1 = &stack
                .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
                .0;

            stack.equal(carry_tmp_0, carry_tmp_1);
            carry = carry_tmp_0.scale(*base).into();
        }

        // constrain native value
        let w0w1: Term<N> = (w0.native() * w0.native()).into();
        let qp: Term<N> = (quotient.native() * -self.rns.wrong_modulus_in_native_modulus).into();
        let r = result.native().sub().into();
        stack.zero_sum_second_degree(&[w0w1, qp, r], N::ZERO);

        result
    }

    pub fn square_add<Stack: SecondDegreeChip<N> + FirstDegreeChip<N>>(
        &self,
        stack: &mut Stack,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        to_add: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let w0 = &self.reduce_if_gt_max_operand(stack, w0);

        // t0 = a0a0
        // t1 = 2 * a0a1
        // t2 = 2 * a0a2 + a1a1
        // t3 = 2 * a0a3 + 2 * a1a2
        // t4 = 2 * a0a4 + 2 * a1a3 + a2a2

        let (result, quotient) = self.rns.mul_witness(w0, w0, &[to_add.clone()]);
        let result = self.range(stack, result, Range::Remainder);
        let quotient = self.range(stack, quotient, Range::MulQuotient);

        let base = self.rns.rsh(1);
        let intermediate = (0..NUMBER_OF_LIMBS)
            .map(|i| {
                (0..i / 2 + 1)
                    .map(|j| {
                        let k = i - j;
                        let base = *base * (if j == k { N::ONE } else { N::from(2) });
                        SecondDegreeScaled::new(&w0.limbs[j], &w0.limbs[k], base).into()
                    })
                    .chain(
                        quotient
                            .limbs
                            .iter()
                            .take(i + 1)
                            .zip(
                                self.rns
                                    .negative_wrong_modulus_decomposed
                                    .iter()
                                    .take(i + 1)
                                    .rev(),
                            )
                            .map(|(q, p)| (Scaled::new(q, *p * base)).into()),
                    )
                    .chain(std::iter::once_with(|| {
                        result.limbs[i].scale(base.neg()).into()
                    }))
                    .chain(std::iter::once_with(|| to_add.limbs[i].scale(*base).into()))
                    .collect::<Vec<Term<_>>>()
            })
            .collect::<Vec<_>>();

        let mut carry_max = BigUint::zero();
        let max_carries = (1..=NUMBER_OF_LIMBS).map(|i| {
            let t = w0
                .max_vals
                .iter()
                .take(i)
                .zip(w0.max_vals.iter().take(i).rev())
                .map(|(w0, w1)| w0 * w1)
                .chain(
                    quotient
                        .max_vals
                        .iter()
                        .take(i)
                        .zip(
                            self.rns
                                .negative_wrong_modulus_decomposed_big
                                .iter()
                                .take(i)
                                .rev(),
                        )
                        .map(|(q, p)| q * p),
                )
                .chain(std::iter::once(to_add.max_vals[i - 1].clone()))
                .chain(std::iter::once(carry_max.clone()))
                .sum::<BigUint>();

            assert!(t < self.rns.native_modulus, "wraps");

            carry_max = t >> LIMB_SIZE;
            carry_max.bits()
        });

        let mut carry: Term<N> = Term::Zero;
        for (terms, carry_max) in intermediate.iter().zip(max_carries) {
            let terms = terms
                .iter()
                .chain(std::iter::once(&carry.clone()))
                .cloned()
                .collect::<Vec<Term<N>>>();

            let carry_tmp_0 = &stack.compose_second_degree(&terms[..], N::ZERO);

            let carry_tmp_1 = &stack
                .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
                .0;

            stack.equal(carry_tmp_0, carry_tmp_1);
            carry = carry_tmp_0.scale(*base).into();
        }

        // constrain native value
        let w0w1: Term<N> = (w0.native() * w0.native()).into();
        let qp: Term<N> = (quotient.native() * -self.rns.wrong_modulus_in_native_modulus).into();
        let r = result.native().sub().into();
        let to_sub = to_add.native().add().into();
        stack.zero_sum_second_degree(&[w0w1, qp, r, to_sub], N::ZERO);

        result
    }

    pub fn mul<Stack: SecondDegreeChip<N> + FirstDegreeChip<N>>(
        &self,
        stack: &mut Stack,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let w0 = self.reduce_if_gt_max_operand(stack, w0);
        let w1 = self.reduce_if_gt_max_operand(stack, w1);

        let (result, quotient) = self.rns.mul_witness(&w0, &w1, &[]);
        let result = self.range(stack, result, Range::Remainder);
        let quotient = self.range(stack, quotient, Range::MulQuotient);

        let base = self.rns.rsh(1);
        let intermediate = (1..=NUMBER_OF_LIMBS).map(|i| {
            let terms = w0
                .limbs
                .iter()
                .take(i)
                .zip(w1.limbs.iter().take(i).rev())
                .map(|(w0, w1)| (w0 * w1).scale(*base).into())
                .chain(
                    quotient
                        .limbs
                        .iter()
                        .take(i)
                        .zip(
                            self.rns
                                .negative_wrong_modulus_decomposed
                                .iter()
                                .take(i)
                                .rev(),
                        )
                        .map(|(q, p)| q.scale(*p * base).into()),
                )
                .chain(std::iter::once(
                    result.limbs[i - 1].scale(base.neg()).into(),
                ))
                .collect::<Vec<Term<_>>>();
            terms
        });

        let mut carry_max = BigUint::zero();
        let max_carries = (1..=NUMBER_OF_LIMBS).map(|i| {
            let t = w0
                .max_vals
                .iter()
                .take(i)
                .zip(w1.max_vals.iter().take(i).rev())
                .map(|(w0, w1)| w0 * w1)
                .chain(
                    quotient
                        .max_vals
                        .iter()
                        .take(i)
                        .zip(
                            self.rns
                                .negative_wrong_modulus_decomposed_big
                                .iter()
                                .take(i)
                                .rev(),
                        )
                        .map(|(q, p)| q * p),
                )
                .chain(std::iter::once(carry_max.clone()))
                .sum::<BigUint>();
            assert!(t < self.rns.native_modulus, "wraps");
            carry_max = t >> LIMB_SIZE;
            carry_max.bits()
        });

        let mut carry: Term<N> = Term::Zero;
        intermediate
            .zip(max_carries)
            .for_each(|(terms, carry_max)| {
                let terms = terms
                    .iter()
                    .chain(std::iter::once(&carry.clone()))
                    .cloned()
                    .collect::<Vec<Term<N>>>();

                let carry_tmp_0 = &stack.compose_second_degree(&terms[..], N::ZERO);

                let carry_tmp_1 = &stack
                    .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
                    .0;

                stack.equal(carry_tmp_0, carry_tmp_1);
                carry = carry_tmp_0.scale(*base).into();
            });

        let w0w1: Term<N> = (w0.native() * w1.native()).into();
        let qp: Term<N> = (quotient.native() * -self.rns.wrong_modulus_in_native_modulus).into();
        let r = result.native().sub().into();
        stack.zero_sum_second_degree(&[w0w1, qp, r], N::ZERO);

        result
    }

    pub fn mul_add<Stack: SecondDegreeChip<N> + FirstDegreeChip<N>>(
        &self,
        stack: &mut Stack,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        to_add: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let w0 = self.reduce_if_gt_max_operand(stack, w0);
        let w1 = self.reduce_if_gt_max_operand(stack, w1);

        let (result, quotient) = self.rns.mul_witness(&w0, &w1, &[to_add.clone()]);
        let result = self.range(stack, result, Range::Remainder);
        let quotient = self.range(stack, quotient, Range::MulQuotient);

        let base = self.rns.rsh(1);
        let intermediate = (1..=NUMBER_OF_LIMBS).map(|i| {
            let terms = w0
                .limbs
                .iter()
                .take(i)
                .zip(w1.limbs.iter().take(i).rev())
                .map(|(w0, w1)| (w0 * w1).scale(*base).into())
                .chain(
                    quotient
                        .limbs
                        .iter()
                        .take(i)
                        .zip(
                            self.rns
                                .negative_wrong_modulus_decomposed
                                .iter()
                                .take(i)
                                .rev(),
                        )
                        .map(|(q, p)| q.scale(*p * base).into()),
                )
                .chain(std::iter::once(
                    result.limbs[i - 1].scale(base.neg()).into(),
                ))
                .chain(std::iter::once(to_add.limbs[i - 1].scale(*base).into()))
                .collect::<Vec<Term<_>>>();
            terms
        });

        let mut carry_max = BigUint::zero();
        let max_carries = (1..=NUMBER_OF_LIMBS).map(|i| {
            let t = w0
                .max_vals
                .iter()
                .take(i)
                .zip(w1.max_vals.iter().take(i).rev())
                .map(|(w0, w1)| w0 * w1)
                .chain(
                    quotient
                        .max_vals
                        .iter()
                        .take(i)
                        .zip(
                            self.rns
                                .negative_wrong_modulus_decomposed_big
                                .iter()
                                .take(i)
                                .rev(),
                        )
                        .map(|(q, p)| q * p),
                )
                .chain(std::iter::once(to_add.max_vals[i - 1].clone()))
                .chain(std::iter::once(carry_max.clone()))
                .sum::<BigUint>();
            assert!(t < self.rns.native_modulus, "wraps");
            carry_max = t >> LIMB_SIZE;
            carry_max.bits()
        });

        let mut carry: Term<N> = Term::Zero;
        intermediate
            .zip(max_carries)
            .for_each(|(terms, carry_max)| {
                let terms = terms
                    .iter()
                    .chain(std::iter::once(&carry.clone()))
                    .cloned()
                    .collect::<Vec<Term<N>>>();

                // println!("terms: {:#?}", terms.len());
                // println!("terms {:#?}", terms);

                let carry_tmp_0 = &stack.compose_second_degree(&terms[..], N::ZERO);

                let carry_tmp_1 = &stack
                    .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
                    .0;

                stack.equal(carry_tmp_0, carry_tmp_1);
                carry = carry_tmp_0.scale(*base).into();
            });

        let w0w1: Term<N> = (w0.native() * w1.native()).into();
        let qp: Term<N> = (quotient.native() * -self.rns.wrong_modulus_in_native_modulus).into();
        let r = result.native().sub().into();
        let to_add = to_add.native().add().into();
        stack.zero_sum_second_degree(&[w0w1, qp, r, to_add], N::ZERO);

        result
    }

    pub fn neg_mul_add_div<Stack: SecondDegreeChip<N> + FirstDegreeChip<N>>(
        &self,
        stack: &mut Stack,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        divisor: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        to_add: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let w0 = self.reduce_if_gt_max_operand(stack, w0);
        let w1 = self.reduce_if_gt_max_operand(stack, w1);

        let (result, quotient) =
            self.rns
                .neg_mul_add_div_witness(&w0, &w1, divisor, &[to_add.clone()]);

        let result = self.range(stack, result, Range::Remainder);
        let quotient = self.range(stack, quotient, Range::MulQuotient);

        let base = self.rns.rsh(1);

        let intermediate = (1..=NUMBER_OF_LIMBS).map(|i| {
            let terms = w0
                .limbs
                .iter()
                .take(i)
                .zip(w1.limbs.iter().take(i).rev())
                .map(|(w0, w1)| (w0 * w1).scale(*base).into())
                .chain(
                    quotient
                        .limbs
                        .iter()
                        .take(i)
                        .zip(
                            self.rns
                                .negative_wrong_modulus_decomposed
                                .iter()
                                .take(i)
                                .rev(),
                        )
                        .map(|(q, p)| q.scale(*p * base).into()),
                )
                .chain(
                    divisor
                        .limbs
                        .iter()
                        .take(i)
                        .zip(result.limbs.iter().take(i).rev())
                        .map(|(w0, w1)| (w0 * w1).scale(*base).into()),
                )
                .chain(std::iter::once_with(|| {
                    to_add.limbs[i - 1].scale(*base).into()
                }))
                .collect::<Vec<Term<_>>>();

            terms
        });

        let mut carry_max = BigUint::zero();
        let max_carries = (1..=NUMBER_OF_LIMBS).map(|i| {
            let t = w0
                .max_vals
                .iter()
                .take(i)
                .zip(w1.max_vals.iter().take(i).rev())
                .map(|(w0, w1)| w0 * w1)
                .chain(
                    quotient
                        .max_vals
                        .iter()
                        .take(i)
                        .zip(
                            self.rns
                                .negative_wrong_modulus_decomposed_big
                                .iter()
                                .take(i)
                                .rev(),
                        )
                        .map(|(q, p)| q * p),
                )
                .chain(
                    divisor
                        .max_vals
                        .iter()
                        .take(i)
                        .zip(result.max_vals.iter().take(i).rev())
                        .map(|(q, p)| q * p),
                )
                .chain(std::iter::once(carry_max.clone()))
                .chain(std::iter::once(to_add.max_vals[i - 1].clone()))
                .sum::<BigUint>();
            assert!(t < self.rns.native_modulus, "wraps");
            carry_max = t >> LIMB_SIZE;
            carry_max.bits()
        });

        let mut carry: Term<N> = Term::Zero;
        intermediate
            .zip(max_carries)
            .for_each(|(terms, carry_max)| {
                let terms = terms
                    .iter()
                    .chain(std::iter::once(&carry.clone()))
                    .cloned()
                    .collect::<Vec<Term<N>>>();

                let carry_tmp_0 = &stack.compose_second_degree(&terms[..], N::ZERO);

                // carry_tmp_0.value().map(|e| {
                //     println!("CARRY {}, {:?}", carry_max, e);
                // });

                #[cfg(feature = "more-info")]
                {
                    println!("negmuldivadd carry: {carry_max}");
                };

                let carry_tmp_1 = &stack
                    .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
                    .0;

                stack.equal(carry_tmp_0, carry_tmp_1);
                carry = carry_tmp_0.scale(*base).into();
            });

        let w0w1: Term<N> = (w0.native() * w1.native()).into();
        let to_add: Term<N> = to_add.native().add().into();
        let qp: Term<N> = (quotient.native() * -self.rns.wrong_modulus_in_native_modulus).into();
        let dz: Term<N> = (divisor.native() * result.native()).into();
        stack.zero_sum_second_degree(&[w0w1, qp, dz, to_add], N::ZERO);

        result
    }

    // ported from barretenberg
    // https://github.com/AztecProtocol/barretenberg/blob/master/cpp/src/barretenberg/stdlib/primitives/bigfield/bigfield_impl.hpp
    pub fn neg_mul_div<Stack: SecondDegreeChip<N> + FirstDegreeChip<N>>(
        &self,
        stack: &mut Stack,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        divisor: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let w0 = self.reduce_if_gt_max_operand(stack, w0);
        let w1 = self.reduce_if_gt_max_operand(stack, w1);

        let (result, quotient) = self.rns.neg_mul_add_div_witness(&w0, &w1, divisor, &[]);

        let result = self.range(stack, result, Range::Remainder);
        let quotient = self.range(stack, quotient, Range::MulQuotient);

        let base = self.rns.rsh(1);

        let intermediate = (1..=NUMBER_OF_LIMBS).map(|i| {
            let terms = w0
                .limbs
                .iter()
                .take(i)
                .zip(w1.limbs.iter().take(i).rev())
                .map(|(w0, w1)| (w0 * w1).scale(*base).into())
                .chain(
                    quotient
                        .limbs
                        .iter()
                        .take(i)
                        .zip(
                            self.rns
                                .negative_wrong_modulus_decomposed
                                .iter()
                                .take(i)
                                .rev(),
                        )
                        .map(|(q, p)| q.scale(*p * base).into()),
                )
                .chain(
                    divisor
                        .limbs
                        .iter()
                        .take(i)
                        .zip(result.limbs.iter().take(i).rev())
                        .map(|(w0, w1)| (w0 * w1).scale(*base).into()),
                )
                .collect::<Vec<Term<_>>>();

            terms
        });

        let mut carry_max = BigUint::zero();
        let max_carries = (1..=NUMBER_OF_LIMBS).map(|i| {
            let t = w0
                .max_vals
                .iter()
                .take(i)
                .zip(w1.max_vals.iter().take(i).rev())
                .map(|(w0, w1)| w0 * w1)
                .chain(
                    quotient
                        .max_vals
                        .iter()
                        .take(i)
                        .zip(
                            self.rns
                                .negative_wrong_modulus_decomposed_big
                                .iter()
                                .take(i)
                                .rev(),
                        )
                        .map(|(q, p)| q * p),
                )
                .chain(
                    divisor
                        .max_vals
                        .iter()
                        .take(i)
                        .zip(result.max_vals.iter().take(i).rev())
                        .map(|(q, p)| q * p),
                )
                .chain(std::iter::once(carry_max.clone()))
                .sum::<BigUint>();
            assert!(t < self.rns.native_modulus, "wraps");
            carry_max = t >> LIMB_SIZE;
            carry_max.bits()
        });

        let mut carry: Term<N> = Term::Zero;
        intermediate
            .zip(max_carries)
            .for_each(|(terms, carry_max)| {
                let terms = terms
                    .iter()
                    .chain(std::iter::once(&carry.clone()))
                    .cloned()
                    .collect::<Vec<Term<N>>>();

                let carry_tmp_0 = &stack.compose_second_degree(&terms[..], N::ZERO);

                // carry_tmp_0.value().map(|e| {
                //     println!("CARRY {}, {:?}", carry_max, e);
                // });

                #[cfg(feature = "more-info")]
                {
                    println!("negmuldivadd carry: {carry_max}");
                };

                let carry_tmp_1 = &stack
                    .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
                    .0;

                stack.equal(carry_tmp_0, carry_tmp_1);
                carry = carry_tmp_0.scale(*base).into();
            });

        let w0w1: Term<N> = (w0.native() * w1.native()).into();
        let qp: Term<N> = (quotient.native() * -self.rns.wrong_modulus_in_native_modulus).into();
        let dz: Term<N> = (divisor.native() * result.native()).into();
        stack.zero_sum_second_degree(&[w0w1, qp, dz], N::ZERO);

        result
    }

    pub fn div_incomplete<Stack: SecondDegreeChip<N> + FirstDegreeChip<N>>(
        &self,
        stack: &mut Stack,
        w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let w0 = &self.reduce_if_gt_max_operand(stack, w0);

        // w0 / w1 = result
        // w0 = w1 * result
        // w0 + p * q = w1 * result
        let (result, quotient, shifter) = self.rns.div_witness(w0, w1);

        let result = self.range(stack, result, Range::Remainder);
        let quotient = self.range(stack, quotient, Range::MulQuotient);

        let base = self.rns.rsh(1);
        let terms = (1..=NUMBER_OF_LIMBS).map(|i| {
            result
                .limbs
                .iter()
                .take(i)
                .zip(w1.limbs.iter().take(i).rev())
                .map(|(r, w1)| (SecondDegreeScaled::new(r, w1, *base)).into())
                .chain(
                    quotient
                        .limbs
                        .iter()
                        .take(i)
                        .zip(
                            self.rns
                                .negative_wrong_modulus_decomposed
                                .iter()
                                .take(i)
                                .rev(),
                        )
                        .map(|(q, p)| (Scaled::new(q, *p * base)).into()),
                )
                .chain(std::iter::once(w0.limbs[i - 1].scale(base.neg()).into()))
                .collect::<Vec<Term<_>>>()
        });

        let mut carry_max = BigUint::zero();
        let max_carries = (1..=NUMBER_OF_LIMBS).map(|i| {
            let t = result
                .max_vals
                .iter()
                .take(i)
                .zip(w1.max_vals.iter().take(i).rev())
                .map(|(r, w1)| r * w1)
                .chain(
                    quotient
                        .max_vals
                        .iter()
                        .take(i)
                        .zip(
                            self.rns
                                .negative_wrong_modulus_decomposed_big
                                .iter()
                                .take(i)
                                .rev(),
                        )
                        .map(|(q, p)| q * p),
                )
                .chain(std::iter::once(carry_max.clone()))
                .chain(std::iter::once(shifter.limbs_big[i - 1].clone()))
                .sum::<BigUint>();

            assert!(t < self.rns.native_modulus, "wraps");
            carry_max = t >> LIMB_SIZE;
            carry_max.bits()
        });

        let mut carry: Term<N> = Term::Zero;

        for ((terms, carry_max), shifter_limb) in terms.zip(max_carries).zip(shifter.limbs) {
            let terms = terms
                .iter()
                .chain(std::iter::once(&carry.clone()))
                .cloned()
                .collect::<Vec<Term<N>>>();

            let carry_tmp_0 = &stack.compose_second_degree(&terms[..], shifter_limb * base);

            #[cfg(feature = "more-info")]
            {
                println!("div carry: {carry_max}");
            };

            let carry_tmp_1 = &stack
                .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
                .0;

            stack.equal(carry_tmp_0, carry_tmp_1);
            carry = carry_tmp_0.scale(*base).into();
        }

        // constrain native value
        let w0w1: Term<N> = (result.native() * w1.native()).into();
        let qp: Term<N> = (quotient.native() * -self.rns.wrong_modulus_in_native_modulus).into();
        let r = w0.native().sub().into();
        let shifter = shifter.native();
        stack.zero_sum_second_degree(&[w0w1, qp, r], shifter);

        result
    }

    // pub fn mul<Stack: CRT256Chip<N, NUMBER_OF_LIMBS> + FirstDegreeChip<N>>(
    //     &self,
    //     stack: &mut Stack,
    //     w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    //     w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    //     to_sub: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    // ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
    //     let (w0, w1) = if std::ptr::eq(w0, w1) {
    //         // square
    //         let w0 = self.reduce_if_gt_max_operand(stack, w0);
    //         let w1 = w0.clone();
    //         (w0, w1)
    //     } else {
    //         // mul
    //         let w0 = self.reduce_if_gt_max_operand(stack, w0);
    //         let w1 = self.reduce_if_gt_max_operand(stack, w1);
    //         (w0, w1)
    //     };

    //     let (result, quotient) = self.rns.multiplication_witness(&w0, &w1, None);

    //     let result = self.range(stack, result, Range::Remainder);
    //     let quotient = self.range(stack, quotient, Range::MulQuotient);

    //     let intermediate = (1..=NUMBER_OF_LIMBS)
    //         .map(|i| {
    //             let terms = w0
    //                 .limbs
    //                 .iter()
    //                 .take(i)
    //                 .zip(w1.limbs.iter().take(i).rev())
    //                 .map(|(w0, w1)| (w0 * w1).into())
    //                 .chain(
    //                     quotient
    //                         .limbs
    //                         .iter()
    //                         .take(i)
    //                         .zip(
    //                             self.rns
    //                                 .negative_wrong_modulus_decomposed
    //                                 .iter()
    //                                 .take(i)
    //                                 .rev(),
    //                         )
    //                         .map(|(q, p)| q.scale(*p).into()),
    //                 )
    //                 .chain(std::iter::once(result.limbs[i - 1].sub().into()))
    //                 .collect::<Vec<Term<_>>>();
    //             Term::compose(&terms[..], N::ZERO)
    //         })
    //         .collect::<Vec<_>>();

    //     let shift = self.rns.right_shifters[1];

    //     let mut carry = N::ZERO;
    //     let carries = intermediate
    //         .iter()
    //         .map(|t| {
    //             t.map(|t| {
    //                 carry = (t + carry) * shift;
    //                 carry
    //             })
    //         })
    //         .collect::<Vec<_>>();

    //     let mut carry_max = BigUint::zero();
    //     let max_carries = (1..=NUMBER_OF_LIMBS).map(|i| {
    //         let t = w0
    //             .max_vals
    //             .iter()
    //             .take(i)
    //             .zip(w1.max_vals.iter().take(i).rev())
    //             .map(|(w0, w1)| w0 * w1)
    //             .chain(
    //                 quotient
    //                     .max_vals
    //                     .iter()
    //                     .take(i)
    //                     .zip(
    //                         self.rns
    //                             .negative_wrong_modulus_decomposed_big
    //                             .iter()
    //                             .take(i)
    //                             .rev(),
    //                     )
    //                     .map(|(q, p)| q * p),
    //             )
    //             .chain(std::iter::once(carry_max.clone()))
    //             .sum::<BigUint>();

    //         assert!(t < self.rns.native_modulus, "wraps");

    //         carry_max = t >> LIMB_SIZE;
    //         carry_max.bits()
    //     });

    //     let carries = carries
    //         .into_iter()
    //         .zip(max_carries)
    //         .map(|(carry, max)| stack.decompose_generic(carry, max as usize, SUBLIMB_SIZE).0)
    //         .collect::<Vec<_>>();

    //     stack.big_mul(
    //         &w0.limbs,
    //         &w1.limbs,
    //         &result.limbs,
    //         &quotient.limbs,
    //         &carries.try_into().unwrap(),
    //         &to_sub.limbs,
    //     );

    //     result
    // }

    // pub fn mul<Stack: CRT256Chip<N, NUMBER_OF_LIMBS> + FirstDegreeChip<N>>(
    //     &self,
    //     stack: &mut Stack,
    //     w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    //     w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    // ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
    //     let (w0, w1) = if std::ptr::eq(w0, w1) {
    //         // square
    //         let w0 = self.reduce_if_gt_max_operand(stack, w0);
    //         let w1 = w0.clone();
    //         (w0, w1)
    //     } else {
    //         // mul
    //         let w0 = self.reduce_if_gt_max_operand(stack, w0);
    //         let w1 = self.reduce_if_gt_max_operand(stack, w1);
    //         (w0, w1)
    //     };

    //     let (result, quotient) = self.rns.multiplication_witness(&w0, &w1, None);

    //     let result = self.range(stack, result, Range::Remainder);
    //     let quotient = self.range(stack, quotient, Range::MulQuotient);

    //     let intermediate = (1..=NUMBER_OF_LIMBS)
    //         .map(|i| {
    //             let terms = w0
    //                 .limbs
    //                 .iter()
    //                 .take(i)
    //                 .zip(w1.limbs.iter().take(i).rev())
    //                 .map(|(w0, w1)| (w0 * w1).into())
    //                 .chain(
    //                     quotient
    //                         .limbs
    //                         .iter()
    //                         .take(i)
    //                         .zip(
    //                             self.rns
    //                                 .negative_wrong_modulus_decomposed
    //                                 .iter()
    //                                 .take(i)
    //                                 .rev(),
    //                         )
    //                         .map(|(q, p)| q.scale(*p).into()),
    //                 )
    //                 .chain(std::iter::once(result.limbs[i - 1].sub().into()))
    //                 .collect::<Vec<Term<_>>>();
    //             Term::compose(&terms[..], N::ZERO)
    //         })
    //         .collect::<Vec<_>>();

    //     let shift = self.rns.right_shifters[1];

    //     let mut carry = N::ZERO;
    //     let carries = intermediate
    //         .iter()
    //         .map(|t| {
    //             t.map(|t| {
    //                 carry = (t + carry) * shift;
    //                 carry
    //             })
    //         })
    //         .collect::<Vec<_>>();

    //     let mut carry_max = BigUint::zero();
    //     let max_carries = (1..=NUMBER_OF_LIMBS).map(|i| {
    //         let t = w0
    //             .max_vals
    //             .iter()
    //             .take(i)
    //             .zip(w1.max_vals.iter().take(i).rev())
    //             .map(|(w0, w1)| w0 * w1)
    //             .chain(
    //                 quotient
    //                     .max_vals
    //                     .iter()
    //                     .take(i)
    //                     .zip(
    //                         self.rns
    //                             .negative_wrong_modulus_decomposed_big
    //                             .iter()
    //                             .take(i)
    //                             .rev(),
    //                     )
    //                     .map(|(q, p)| q * p),
    //             )
    //             .chain(std::iter::once(carry_max.clone()))
    //             .sum::<BigUint>();

    //         assert!(t < self.rns.native_modulus, "wraps");

    //         carry_max = t >> LIMB_SIZE;
    //         carry_max.bits()
    //     });

    //     let carries = carries
    //         .into_iter()
    //         .zip(max_carries)
    //         .map(|(carry, max)| stack.decompose_generic(carry, max as usize, SUBLIMB_SIZE).0)
    //         .collect::<Vec<_>>();

    //     stack.big_mul(
    //         &w0.limbs,
    //         &w1.limbs,
    //         &result.limbs,
    //         &quotient.limbs,
    //         &carries.try_into().unwrap(),
    //     );

    //     result
    // }

    // pub fn div_incomplete<Stack: CRT256Chip<N, NUMBER_OF_LIMBS> + FirstDegreeChip<N>>(
    //     &self,
    //     stack: &mut Stack,
    //     w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    //     w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    // ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
    //     let (result, quotient) = self.rns.division_witness(&w0, &w1);

    //     let result = self.range(stack, result, Range::Remainder);
    //     let quotient = self.range(stack, quotient, Range::MulQuotient);

    //     let intermediate = (1..=NUMBER_OF_LIMBS)
    //         .map(|i| {
    //             let terms = result
    //                 .limbs
    //                 .iter()
    //                 .take(i)
    //                 .zip(w1.limbs.iter().take(i).rev())
    //                 .map(|(r, w1)| (r * w1).into())
    //                 .chain(
    //                     quotient
    //                         .limbs
    //                         .iter()
    //                         .take(i)
    //                         .zip(
    //                             self.rns
    //                                 .negative_wrong_modulus_decomposed
    //                                 .iter()
    //                                 .take(i)
    //                                 .rev(),
    //                         )
    //                         .map(|(q, p)| q.scale(*p).into()),
    //                 )
    //                 .chain(std::iter::once(w0.limbs[i - 1].sub().into()))
    //                 .collect::<Vec<Term<_>>>();
    //             Term::compose(&terms[..], N::ZERO)
    //         })
    //         .collect::<Vec<_>>();

    //     let shift = self.rns.right_shifters[1];

    //     let mut carry = N::ZERO;
    //     let carries = intermediate
    //         .iter()
    //         .map(|t| {
    //             t.map(|t| {
    //                 carry = (t + carry) * shift;

    //                 carry
    //             })
    //         })
    //         .collect::<Vec<_>>();

    //     let mut carry_max = BigUint::zero();
    //     let max_carries = (1..=NUMBER_OF_LIMBS).map(|i| {
    //         let t = w0
    //             .max_vals
    //             .iter()
    //             .take(i)
    //             .zip(w1.max_vals.iter().take(i).rev())
    //             .map(|(w0, w1)| w0 * w1)
    //             .chain(
    //                 quotient
    //                     .max_vals
    //                     .iter()
    //                     .take(i)
    //                     .zip(
    //                         self.rns
    //                             .negative_wrong_modulus_decomposed_big
    //                             .iter()
    //                             .take(i)
    //                             .rev(),
    //                     )
    //                     .map(|(q, p)| q * p),
    //             )
    //             .chain(std::iter::once(carry_max.clone()))
    //             .sum::<BigUint>();

    //         // TODO: remove, it's fatal if pass
    //         assert!(t < self.rns.native_modulus, "wraps");

    //         carry_max = t >> LIMB_SIZE;
    //         carry_max.bits()
    //     });

    //     let carries = carries
    //         .into_iter()
    //         .zip(max_carries)
    //         .map(|(carry, max)| stack.decompose_generic(carry, max as usize, SUBLIMB_SIZE).0)
    //         .collect::<Vec<_>>();

    //     let limbs = (0..NUMBER_OF_LIMBS)
    //         .map(|_| stack.new_witness(Value::known(N::ZERO)))
    //         .collect::<Vec<_>>();
    //     let max_vals = (0..NUMBER_OF_LIMBS)
    //         .map(|_| BigUint::zero())
    //         .collect::<Vec<_>>();
    //     let zero: Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> = Integer::new(
    //         &limbs.try_into().unwrap(),
    //         &max_vals.try_into().unwrap(),
    //         Value::known(BigUint::zero()),
    //     );

    //     stack.big_mul(
    //         &result.limbs,
    //         &w1.limbs,
    //         &w0.limbs,
    //         &quotient.limbs,
    //         &carries.try_into().unwrap(),
    //         &zero.limbs,
    //     );

    //     result
    // }

    // for (terms, carry_max) in terms.iter().zip(max_carries) {
    //     let terms = terms
    //         .iter()
    //         .chain(std::iter::once(&carry.clone()))
    //         .cloned()
    //         .collect::<Vec<Term<N>>>();

    //     let carry_tmp_0 = &stack.compose_second_degree(&terms[..], N::ZERO);

    //     let carry_tmp_1 = &stack
    //         .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
    //         .0;

    //     stack.equal(carry_tmp_0, carry_tmp_1);
    //     carry = carry_tmp_0.scale(*base).into();
    // }

    // let base = self.rns.rsh(1);
    // let terms = (1..=NUMBER_OF_LIMBS)
    //     .map(|i| {
    //         w0.limbs
    //             .iter()
    //             .take(i)
    //             .zip(w1.limbs.iter().take(i).rev())
    //             .map(|(w0, w1)| (SecondDegreeScaled::new(w0, w1, *base)).into())
    //             .chain(
    //                 quotient
    //                     .limbs
    //                     .iter()
    //                     .take(i)
    //                     .zip(
    //                         self.rns
    //                             .negative_wrong_modulus_decomposed
    //                             .iter()
    //                             .take(i)
    //                             .rev(),
    //                     )
    //                     .map(|(q, p)| (Scaled::new(q, *p * base)).into()),
    //             )
    //             .chain(std::iter::once(result.limbs[i - 1].scale(base.neg()).into()))
    //             .collect::<Vec<Term<_>>>()
    //     })
    //     .collect::<Vec<_>>();

    // // TODO: work with bits?
    // let mut carry_max = BigUint::zero();
    // let max_carries = (1..=NUMBER_OF_LIMBS).map(|i| {
    //     let t = w0
    //         .max_vals
    //         .iter()
    //         .take(i)
    //         .zip(w1.max_vals.iter().take(i).rev())
    //         .map(|(w0, w1)| w0 * w1)
    //         .chain(
    //             quotient
    //                 .max_vals
    //                 .iter()
    //                 .take(i)
    //                 .zip(
    //                     self.rns
    //                         .negative_wrong_modulus_decomposed_big
    //                         .iter()
    //                         .take(i)
    //                         .rev(),
    //                 )
    //                 .map(|(q, p)| q * p),
    //         )
    //         .chain(std::iter::once(carry_max.clone()))
    //         .sum::<BigUint>();

    //     assert!(t < self.rns.native_modulus, "wraps");

    //     carry_max = t >> LIMB_SIZE;
    //     carry_max.bits()
    // });

    // let mut carry: Term<N> = Term::Zero;

    // for (terms, carry_max) in terms.iter().zip(max_carries) {
    //     let terms = terms
    //         .iter()
    //         .chain(std::iter::once(&carry.clone()))
    //         .cloned()
    //         .collect::<Vec<Term<N>>>();

    //     let carry_tmp_0 = &stack.compose_second_degree(&terms[..], N::ZERO);

    //     let carry_tmp_1 = &stack
    //         .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
    //         .0;

    //     stack.equal(carry_tmp_0, carry_tmp_1);
    //     carry = carry_tmp_0.scale(*base).into();
    // }

    // // constrain native value
    // let w0w1: Term<N> = (w0.native() * w1.native()).into();
    // let qp: Term<N> = (quotient.native() * -self.rns.wrong_modulus_in_native_modulus).into();
    // let r = result.native().sub().into();
    // stack.zero_sum_second_degree(&[w0w1, qp, r], N::ZERO);

    // result

    // pub fn mul_constant(
    //     &self,
    //     stack: &mut CRTChip<N, NUMBER_OF_LIMBS>,
    //     w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    //     constant: &ConstantInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    // ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
    //     let w0 = &self.reduce_if_gt_max_operand(stack, w0);

    //     let (result, quotient) = self.rns.constant_multiplication_witness(w0, constant);
    //     // range new witness integers
    //     let result = self.range(stack, result, Range::Remainder);
    //     let quotient = self.range(stack, quotient, Range::MulQuotient);

    //     // collect combination terms

    //     let base = self.rns.rsh(1);
    //     let terms = (1..=NUMBER_OF_LIMBS).map(|i| {
    //         w0.limbs
    //             .iter()
    //             .take(i)
    //             .zip(constant.limbs.iter().take(i).rev())
    //             .map(|(w0, w1)| (Scaled::new(w0, *base * w1)))
    //             .chain(
    //                 quotient
    //                     .limbs
    //                     .iter()
    //                     .take(i)
    //                     .zip(
    //                         self.rns
    //                             .negative_wrong_modulus_decomposed
    //                             .iter()
    //                             .take(i)
    //                             .rev(),
    //                     )
    //                     .map(|(q, p)| (Scaled::new(q, *p * base))),
    //             )
    //             .chain(std::iter::once(result.limbs[i - 1].scale(base.neg())))
    //             .collect::<Vec<Scaled<_>>>()
    //     });

    //     let mut carry_max = BigUint::zero();
    //     let max_carries = (1..=NUMBER_OF_LIMBS).map(|i| {
    //         let t = w0
    //             .max_vals
    //             .iter()
    //             .take(i)
    //             .zip(constant.limbs_big.iter().take(i).rev())
    //             .map(|(w0, w1)| w0 * w1)
    //             .chain(
    //                 quotient
    //                     .max_vals
    //                     .iter()
    //                     .take(i)
    //                     .zip(
    //                         self.rns
    //                             .negative_wrong_modulus_decomposed_big
    //                             .iter()
    //                             .take(i)
    //                             .rev(),
    //                     )
    //                     .map(|(q, p)| q * p),
    //             )
    //             .chain(std::iter::once(carry_max.clone()))
    //             .sum::<BigUint>();

    //         assert!(t < self.rns.native_modulus, "wraps");

    //         carry_max = t >> LIMB_SIZE;
    //         carry_max.bits()
    //     });

    //     let mut carry: Scaled<N> = Scaled::dummy();

    //     for (terms, carry_max) in terms.zip(max_carries) {
    //         let terms = terms
    //             .iter()
    //             .chain(std::iter::once(&carry.clone()))
    //             .cloned()
    //             .collect::<Vec<Scaled<N>>>();

    //         let carry_tmp_0 = &stack.compose(&terms[..], N::ZERO);

    //         let carry_tmp_1 = &stack
    //             .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
    //             .0;

    //         stack.equal(carry_tmp_0, carry_tmp_1);
    //         carry = carry_tmp_0.scale(*base);
    //     }

    //     // constrain native value
    //     let w0w1: Scaled<N> = w0.native().scale(constant.native);
    //     let qp: Scaled<N> = quotient.native() * -self.rns.wrong_modulus_in_native_modulus;
    //     let r = result.native().sub();
    //     stack.zero_sum(&[w0w1, qp, r], N::ZERO);

    //     result
    // }

    // pub fn square(
    //     &self,
    //     stack: &mut CRTChip<N, NUMBER_OF_LIMBS>,
    //     w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    // ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
    //     let w0 = &self.reduce_if_gt_max_operand(stack, w0);

    //     // t0 = a0a0
    //     // t1 = 2 * a0a1
    //     // t2 = 2 * a0a2 + a1a1
    //     // t3 = 2 * a0a3 + 2 * a1a2
    //     // t4 = 2 * a0a4 + 2 * a1a3 + a2a2

    //     let (result, quotient) = self.rns.multiplication_witness(w0, w0, None);
    //     let result = self.range(stack, result, Range::Remainder);
    //     let quotient = self.range(stack, quotient, Range::MulQuotient);

    //     let base = self.rns.rsh(1);
    //     let terms = (0..NUMBER_OF_LIMBS)
    //         .map(|i| {
    //             (0..i / 2 + 1)
    //                 .map(|j| {
    //                     let k = i - j;
    //                     let base = *base * (if j == k { N::ONE } else { N::from(2) });
    //                     SecondDegreeScaled::new(&w0.limbs[j], &w0.limbs[k], base).into()
    //                 })
    //                 .chain(
    //                     quotient
    //                         .limbs
    //                         .iter()
    //                         .take(i + 1)
    //                         .zip(
    //                             self.rns
    //                                 .negative_wrong_modulus_decomposed
    //                                 .iter()
    //                                 .take(i + 1)
    //                                 .rev(),
    //                         )
    //                         .map(|(q, p)| (Scaled::new(q, *p * base)).into()),
    //                 )
    //                 .chain(std::iter::once_with(|| {
    //                     result.limbs[i].scale(base.neg()).into()
    //                 }))
    //                 .collect::<Vec<Term<_>>>()
    //         })
    //         .collect::<Vec<_>>();

    //     let mut carry_max = BigUint::zero();
    //     let max_carries = (1..=NUMBER_OF_LIMBS).map(|i| {
    //         let t = w0
    //             .max_vals
    //             .iter()
    //             .take(i)
    //             .zip(w0.max_vals.iter().take(i).rev())
    //             .map(|(w0, w1)| w0 * w1)
    //             .chain(
    //                 quotient
    //                     .max_vals
    //                     .iter()
    //                     .take(i)
    //                     .zip(
    //                         self.rns
    //                             .negative_wrong_modulus_decomposed_big
    //                             .iter()
    //                             .take(i)
    //                             .rev(),
    //                     )
    //                     .map(|(q, p)| q * p),
    //             )
    //             .chain(std::iter::once(carry_max.clone()))
    //             .sum::<BigUint>();

    //         assert!(t < self.rns.native_modulus, "wraps");

    //         carry_max = t >> LIMB_SIZE;
    //         carry_max.bits()
    //     });

    //     let mut carry: Term<N> = Term::Zero;

    //     for (terms, carry_max) in terms.iter().zip(max_carries) {
    //         let terms = terms
    //             .iter()
    //             .chain(std::iter::once(&carry.clone()))
    //             .cloned()
    //             .collect::<Vec<Term<N>>>();

    //         let carry_tmp_0 = &stack.compose_second_degree(&terms[..], N::ZERO);

    //         let carry_tmp_1 = &stack
    //             .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
    //             .0;

    //         stack.equal(carry_tmp_0, carry_tmp_1);
    //         carry = carry_tmp_0.scale(*base).into();
    //     }

    //     // constrain native value
    //     let w0w1: Term<N> = (w0.native() * w0.native()).into();
    //     let qp: Term<N> = (quotient.native() * -self.rns.wrong_modulus_in_native_modulus).into();
    //     let r = result.native().sub().into();
    //     stack.zero_sum_second_degree(&[w0w1, qp, r], N::ZERO);

    //     result
    // }

    // pub fn div_incomplete(
    //     &self,
    //     stack: &mut CRTChip<N, NUMBER_OF_LIMBS>,
    //     w0: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    //     w1: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    // ) -> Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
    //     let w0 = &self.reduce_if_gt_max_operand(stack, w0);

    //     // w0 / w1 = result
    //     // w0 = w1 * result
    //     // w0 + p * q = w1 * result
    //     let (result, quotient) = self.rns.division_witness(w0, w1);

    //     let result = self.range(stack, result, Range::Remainder);
    //     let quotient = self.range(stack, quotient, Range::MulQuotient);

    //     let base = self.rns.rsh(1);
    //     let terms = (1..=NUMBER_OF_LIMBS).map(|i| {
    //         result
    //             .limbs
    //             .iter()
    //             .take(i)
    //             .zip(w1.limbs.iter().take(i).rev())
    //             .map(|(r, w1)| (SecondDegreeScaled::new(r, w1, *base)).into())
    //             .chain(
    //                 quotient
    //                     .limbs
    //                     .iter()
    //                     .take(i)
    //                     .zip(
    //                         self.rns
    //                             .negative_wrong_modulus_decomposed
    //                             .iter()
    //                             .take(i)
    //                             .rev(),
    //                     )
    //                     .map(|(q, p)| (Scaled::new(q, *p * base)).into()),
    //             )
    //             .chain(std::iter::once(w0.limbs[i - 1].scale(base.neg()).into()))
    //             .collect::<Vec<Term<_>>>()
    //     });

    //     let mut carry_max = BigUint::zero();
    //     let max_carries = (1..=NUMBER_OF_LIMBS).map(|i| {
    //         let t = result
    //             .max_vals
    //             .iter()
    //             .take(i)
    //             .zip(w1.max_vals.iter().take(i).rev())
    //             .map(|(r, w1)| r * w1)
    //             .chain(
    //                 quotient
    //                     .max_vals
    //                     .iter()
    //                     .take(i)
    //                     .zip(
    //                         self.rns
    //                             .negative_wrong_modulus_decomposed_big
    //                             .iter()
    //                             .take(i)
    //                             .rev(),
    //                     )
    //                     .map(|(q, p)| q * p),
    //             )
    //             .chain(std::iter::once(carry_max.clone()))
    //             .sum::<BigUint>();

    //         assert!(t < self.rns.native_modulus, "wraps");

    //         carry_max = t >> LIMB_SIZE;
    //         carry_max.bits()
    //     });

    //     let mut carry: Term<N> = Term::Zero;

    //     for (terms, carry_max) in terms.zip(max_carries) {
    //         let terms = terms
    //             .iter()
    //             .chain(std::iter::once(&carry.clone()))
    //             .cloned()
    //             .collect::<Vec<Term<N>>>();

    //         let carry_tmp_0 = &stack.compose_second_degree(&terms[..], N::ZERO);

    //         let carry_tmp_1 = &stack
    //             .decompose_generic(carry_tmp_0.value(), carry_max as usize, SUBLIMB_SIZE)
    //             .0;

    //         stack.equal(carry_tmp_0, carry_tmp_1);
    //         carry = carry_tmp_0.scale(*base).into();
    //     }

    //     // constrain native value
    //     let w0w1: Term<N> = (result.native() * w1.native()).into();
    //     let qp: Term<N> = (quotient.native() * -self.rns.wrong_modulus_in_native_modulus).into();
    //     let r = w0.native().sub().into();
    //     stack.zero_sum_second_degree(&[w0w1, qp, r], N::ZERO);

    //     result
    // }
}
