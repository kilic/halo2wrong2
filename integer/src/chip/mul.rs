use crate::chip::IntegerChip;
use crate::integer::{Integer, Range};
use crate::schoolbook;
use circuitry::chip::range::RangeChip;
use circuitry::chip::second_degree::SecondDegreeChip;
use circuitry::chip::Core;
use circuitry::stack::Stack;
use circuitry::witness::{Composable, Scaled, SecondDegreeScaled, Term, Witness};
use ff::PrimeField;

macro_rules! div_ceil {
    ($a:expr, $b:expr) => {
        (($a - 1) / $b) + 1
    };
}

impl<W: PrimeField, N: PrimeField + Ord> IntegerChip<W, N> {
    pub fn square(
        &self,
        stack: &mut Stack<N>,
        w0: &Integer<W, N>,
        to_add: &[&Integer<W, N>],
    ) -> Integer<W, N> {
        let w0 = &self.reduce_if_necessary(stack, w0);

        let (result, quotient) = self.rns.mul_witness(w0, w0, to_add);
        let result = self.range(stack, &result, Range::Remainder);
        let quotient = self.range(stack, &quotient, Range::MulQuotient);

        // t0 = a0a0
        // t1 = 2 * a0a1
        // t2 = 2 * a0a2 + a1a1
        // t3 = 2 * a0a3 + 2 * a1a2
        // t4 = 2 * a0a4 + 2 * a1a3 + a2a2

        {
            let max_carries = {
                let to_add = to_add
                    .iter()
                    .map(|to_add| to_add.max_vals())
                    .collect::<Vec<_>>();

                self.rns
                    .mul_max_carries(w0.max_vals(), w0.max_vals(), &to_add)
            };

            let base = self.rns.rsh(1);

            let ww =
                schoolbook::<Witness<N>, Witness<N>, SecondDegreeScaled<N>>(w0.limbs(), w0.limbs());

            let ww = ww.iter().map(|t| {
                let off = div_ceil!(t.len(), 2);

                t.iter().take(off).enumerate().map(move |(i, e)| {
                    if t.len() & 1 == 1 && i == off - 1 {
                        e.scale(*base).as_term()
                    } else {
                        e.scale(*base * N::from(2)).as_term()
                    }
                })
            });

            let pq = schoolbook::<Witness<N>, N, Scaled<N>>(
                quotient.limbs(),
                &self.rns.neg_wrong_limbs_in_binary,
            );
            let pq = pq
                .iter()
                .map(|t| t.iter().map(|e| e.scale(*base).as_term()));

            let result = result
                .limbs()
                .iter()
                .map(|e| e.scale(base.neg()).as_term())
                .chain(std::iter::repeat(Term::Zero));

            let to_add = to_add
                .iter()
                .map(|to_add| {
                    to_add
                        .limbs()
                        .iter()
                        .map(|e| e.scale(*base).as_term())
                        .chain(std::iter::repeat(Term::Zero))
                        .take(self.rns.number_of_carries)
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();

            // and transpose for each level of carries
            let to_add = (0..self.rns.number_of_carries)
                .map(|i| to_add.iter().map(|e| e[i].clone()).collect::<Vec<_>>())
                .collect::<Vec<_>>();

            let mut carry: Term<N> = Term::Zero;
            ww.zip(pq)
                .zip(result)
                .zip(to_add)
                .zip(max_carries.iter())
                .take(self.rns.number_of_carries)
                .for_each(|((((ww, pq), result), to_add), max_carry)| {
                    let terms = ww
                        .chain(pq)
                        .chain(std::iter::once(result))
                        .chain(to_add)
                        .chain(std::iter::once(carry.clone()))
                        .collect::<Vec<_>>();

                    let carry_0 = &stack.compose_second_degree(&terms[..], N::ZERO);
                    let carry_1 = &stack
                        .decompose(carry_0.value(), *max_carry, self.sublimb_size)
                        .0;

                    stack.equal(carry_0, carry_1);
                    carry = carry_0.scale(*base).into();
                })
        }

        // 3. constrain native value

        let terms: Vec<Term<N>> = to_add
            .iter()
            .map(|to_add| to_add.native().add().into())
            .chain(std::iter::once((w0.native() * w0.native()).into()))
            .chain(std::iter::once(
                (quotient.native() * -self.rns.wrong_in_native).into(),
            ))
            .chain(std::iter::once(result.native().sub().into()))
            .collect();

        stack.zero_sum_second_degree(&terms, N::ZERO);

        result
    }

    pub fn mul(
        &self,
        stack: &mut Stack<N>,
        w0: &Integer<W, N>,
        w1: &Integer<W, N>,
        to_add: &[&Integer<W, N>],
    ) -> Integer<W, N> {
        let w0 = &self.reduce_if_necessary(stack, w0);
        let w1 = &self.reduce_if_necessary(stack, w1);

        // 1. find and range new witneses

        let (result, quotient) = self.rns.mul_witness(w0, w1, to_add);
        let result = self.range(stack, &result, Range::Remainder);
        let quotient = self.range(stack, &quotient, Range::MulQuotient);

        // 2. constrain carries

        {
            let max_carries = {
                let to_add = to_add
                    .iter()
                    .map(|to_add| to_add.max_vals())
                    .collect::<Vec<_>>();

                self.rns
                    .mul_max_carries(w0.max_vals(), w1.max_vals(), &to_add)
            };

            let base = self.rns.rsh(1);

            let ww =
                schoolbook::<Witness<N>, Witness<N>, SecondDegreeScaled<N>>(w0.limbs(), w1.limbs());
            let ww = ww
                .iter()
                .map(|t| t.iter().map(|e| e.scale(*base).as_term()));

            let pq = schoolbook::<Witness<N>, N, Scaled<N>>(
                quotient.limbs(),
                &self.rns.neg_wrong_limbs_in_binary,
            );
            let pq = pq
                .iter()
                .map(|t| t.iter().map(|e| e.scale(*base).as_term()));

            let result = result
                .limbs()
                .iter()
                .map(|e| e.scale(base.neg()).as_term())
                .chain(std::iter::repeat(Term::Zero));

            let to_add = to_add
                .iter()
                .map(|to_add| {
                    to_add
                        .limbs()
                        .iter()
                        .map(|e| e.scale(*base).as_term())
                        .chain(std::iter::repeat(Term::Zero))
                        .take(self.rns.number_of_carries)
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();

            // and transpose for each level of carries
            let to_add = (0..self.rns.number_of_carries)
                .map(|i| to_add.iter().map(|e| e[i].clone()).collect::<Vec<_>>())
                .collect::<Vec<_>>();

            let mut carry: Term<N> = Term::Zero;
            ww.zip(pq)
                .zip(result)
                .zip(to_add)
                .zip(max_carries.iter())
                .take(self.rns.number_of_carries)
                .for_each(|((((ww, pq), result), to_add), max_carry)| {
                    let terms = ww
                        .chain(pq)
                        .chain(std::iter::once(result))
                        .chain(to_add)
                        .chain(std::iter::once(carry.clone()))
                        .collect::<Vec<_>>();

                    let carry_0 = &stack.compose_second_degree(&terms[..], N::ZERO);

                    let carry_1 = &stack
                        .decompose(carry_0.value(), *max_carry, self.sublimb_size)
                        .0;

                    stack.equal(carry_0, carry_1);
                    carry = carry_0.scale(*base).into();
                })
        }

        // 3. constrain native value

        let terms: Vec<Term<N>> = to_add
            .iter()
            .map(|to_add| to_add.native().add().into())
            .chain(std::iter::once((w0.native() * w1.native()).into()))
            .chain(std::iter::once(
                (quotient.native() * -self.rns.wrong_in_native).into(),
            ))
            .chain(std::iter::once(result.native().sub().into()))
            .collect();

        stack.zero_sum_second_degree(&terms, N::ZERO);

        result
    }

    pub fn div(
        &self,
        stack: &mut Stack<N>,
        w0: &Integer<W, N>,
        w1: &Integer<W, N>,
    ) -> Integer<W, N> {
        assert!(!self.is_gt_max_operand(w0));

        // 1. find and range new witneses

        let (result, quotient, shifter) = self.rns.div_witness(w0, w1);

        let result = self.range(stack, &result, Range::Remainder);
        let quotient = self.range(stack, &quotient, Range::MulQuotient);

        // 2. constrain carries

        {
            let max_carries =
                self.rns
                    .mul_max_carries(result.max_vals(), w1.max_vals(), &[shifter.big_limbs()]);

            let base = self.rns.rsh(1);

            let ww = schoolbook::<Witness<N>, Witness<N>, SecondDegreeScaled<N>>(
                result.limbs(),
                w1.limbs(),
            );

            let ww = ww
                .iter()
                .map(|t| t.iter().map(|e| e.scale(*base).as_term()));

            let pq = schoolbook::<Witness<N>, N, Scaled<N>>(
                quotient.limbs(),
                &self.rns.neg_wrong_limbs_in_binary,
            );

            let pq = pq
                .iter()
                .map(|t| t.iter().map(|e| e.scale(*base).as_term()));

            let result = w0
                .limbs()
                .iter()
                .map(|e| e.scale(base.neg()).as_term())
                .chain(std::iter::repeat(Term::Zero));

            let mut carry: Term<N> = Term::Zero;

            ww.zip(pq)
                .zip(result)
                .zip(shifter.limbs())
                .zip(max_carries.iter())
                .take(self.rns.number_of_carries)
                .for_each(|((((ww, pq), result), shifter), max_carry)| {
                    let terms = ww
                        .chain(pq)
                        .chain(std::iter::once(result))
                        .chain(std::iter::once(carry.clone()))
                        .collect::<Vec<_>>();

                    let carry_0 = &stack.compose_second_degree(&terms[..], *shifter * base);

                    let carry_1 = &stack
                        .decompose(carry_0.value(), *max_carry, self.sublimb_size)
                        .0;

                    stack.equal(carry_0, carry_1);
                    carry = carry_0.scale(*base).into();
                })
        }

        // 3. constrain native value

        let w0w1: Term<N> = (result.native() * w1.native()).into();
        let pq: Term<N> = (quotient.native() * -self.rns.wrong_in_native).into();
        let r = w0.native().sub().into();
        stack.zero_sum_second_degree(&[w0w1, pq, r], shifter.native());

        result
    }

    // ported from barretenberg

    pub fn neg_mul_div(
        &self,
        stack: &mut Stack<N>,
        w0: &Integer<W, N>,
        w1: &Integer<W, N>,
        divisor: &Integer<W, N>,
        to_add: &[&Integer<W, N>],
    ) -> Integer<W, N> {
        assert!(!self.is_gt_max_operand(w0));
        assert!(!self.is_gt_max_operand(w1));
        assert!(!self.is_gt_max_operand(divisor));

        // 1. find and range new witneses

        let (result, quotient) = self.rns.neg_mul_add_div_witness(w0, w1, divisor, to_add);

        let result = self.range(stack, &result, Range::Remainder);
        let quotient = self.range(stack, &quotient, Range::MulQuotient);

        // 2. constrain carries

        {
            let max_carries = {
                let to_add = to_add
                    .iter()
                    .map(|to_add| to_add.max_vals())
                    .collect::<Vec<_>>();

                self.rns.neg_mul_div_max_carries(
                    w0.max_vals(),
                    w0.max_vals(),
                    divisor.max_vals(),
                    &to_add,
                )
            };

            let base = self.rns.rsh(1);

            let ww =
                schoolbook::<Witness<N>, Witness<N>, SecondDegreeScaled<N>>(w0.limbs(), w1.limbs());

            let ww = ww
                .iter()
                .map(|t| t.iter().map(|e| e.scale(*base).as_term()));

            let pq = schoolbook::<Witness<N>, N, Scaled<N>>(
                quotient.limbs(),
                &self.rns.neg_wrong_limbs_in_binary,
            );

            let pq = pq
                .iter()
                .map(|t| t.iter().map(|e| e.scale(*base).as_term()));

            let rd = schoolbook::<Witness<N>, Witness<N>, _>(result.limbs(), divisor.limbs());

            let rd = rd
                .iter()
                .map(|t| t.iter().map(|e| e.scale(*base).as_term()));

            let to_add = to_add
                .iter()
                .map(|to_add| {
                    to_add
                        .limbs()
                        .iter()
                        .map(|e| e.scale(*base).as_term())
                        .chain(std::iter::repeat(Term::Zero))
                        .take(self.rns.number_of_carries)
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();

            // and transpose for each level of carries
            let to_add = (0..self.rns.number_of_carries)
                .map(|i| to_add.iter().map(|e| e[i].clone()).collect::<Vec<_>>())
                .collect::<Vec<_>>();

            let mut carry: Term<N> = Term::Zero;

            ww.zip(pq)
                .zip(rd)
                .zip(to_add)
                .zip(max_carries.iter())
                .take(self.rns.number_of_carries)
                .for_each(|((((ww, pq), rd), to_add), max_carry)| {
                    let terms = ww
                        .chain(pq)
                        .chain(rd)
                        .chain(to_add)
                        .chain(std::iter::once(carry.clone()))
                        .collect::<Vec<_>>();

                    let carry_0 = &stack.compose_second_degree(&terms[..], N::ZERO);

                    let carry_1 = &stack
                        .decompose(carry_0.value(), *max_carry, self.sublimb_size)
                        .0;

                    stack.equal(carry_0, carry_1);
                    carry = carry_0.scale(*base).into();
                })
        }

        // 3. constrain native value

        let terms: Vec<Term<N>> = to_add
            .iter()
            .map(|to_add| to_add.native().add().into())
            .chain(std::iter::once((w0.native() * w1.native()).into()))
            .chain(std::iter::once(
                (quotient.native() * -self.rns.wrong_in_native).into(),
            ))
            .chain(std::iter::once((divisor.native() * result.native()).into()))
            .collect();

        stack.zero_sum_second_degree(&terms, N::ZERO);

        result
    }
}
