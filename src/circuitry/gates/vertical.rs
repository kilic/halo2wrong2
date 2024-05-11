use super::{range::RangeGate, GateLayout};
use crate::circuitry::{
    witness::{Composable, Witness},
    LayoutCtx,
};
use ff::PrimeField;
use halo2::{
    circuit::{Layouter, Value},
    plonk::{
        Advice, Challenge, Column, ConstraintSystem, Constraints, Error, FirstPhase, Fixed,
        SecondPhase, Selector,
    },
    poly::Rotation,
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug)]
pub struct VerticalGate<const W: usize> {
    pub(crate) base: Column<Fixed>,
    pub(crate) range_gate: RangeGate,
    pub(crate) advices: [Column<Advice>; W],
    pub(crate) acc: Column<Advice>,
    pub(crate) challenges: Vec<Challenge>,
    pub(crate) acc_selector: Selector,
    pub(crate) eq_selector: Selector,
}

impl<const W: usize> VerticalGate<W> {
    pub fn configure<F: PrimeField>(
        meta: &mut ConstraintSystem<F>,
        range_gate: &RangeGate,
        advices: [Column<Advice>; W],
    ) -> Self {
        let acc_selector = meta.selector();
        let eq_selector = meta.selector();

        let challenges = (0..advices.len() - 1)
            .map(|_| meta.challenge_usable_after(FirstPhase))
            .collect::<Vec<_>>();

        let base = meta.fixed_column();
        // let acc = meta.advice_column_in(SecondPhase);
        let acc = if W > 1 {
            meta.advice_column_in(SecondPhase)
        } else {
            meta.advice_column()
        };

        advices
            .iter()
            .for_each(|advice| meta.enable_equality(*advice));

        meta.create_gate("acc", |meta| {
            let acc_selector = meta.query_selector(acc_selector);

            let challenges = challenges
                .iter()
                .map(|challenge| meta.query_challenge(*challenge))
                .collect::<Vec<_>>();

            let advices = advices
                .iter()
                .map(|advice| meta.query_advice(*advice, Rotation::cur()))
                .collect::<Vec<_>>();

            let advice_rlc = advices.iter().skip(1).zip(challenges.iter()).fold(
                advices.first().unwrap().clone(),
                |acc, (advice, challenge)| acc + advice.clone() * challenge.clone(),
            );

            let base = meta.query_fixed(base, Rotation::cur());

            let acc_prev = meta.query_advice(acc, Rotation::prev());
            let acc = meta.query_advice(acc, Rotation::cur());

            let term = base * advice_rlc;
            let expr = acc_prev + term - acc.clone();

            Constraints::with_selector(acc_selector, std::iter::once(expr))
        });

        meta.create_gate("eq", |meta| {
            let eq_selector = meta.query_selector(eq_selector);
            let acc = meta.query_advice(acc, Rotation::cur());
            Constraints::with_selector(eq_selector, std::iter::once(acc))
        });

        VerticalGate {
            challenges,
            base,
            advices,
            acc,
            range_gate: range_gate.clone(),
            acc_selector,
            eq_selector,
        }
    }

    pub fn advice_columns(&self) -> [Column<Advice>; W] {
        self.advices
    }

    pub fn acc_column(&self) -> Column<Advice> {
        self.acc
    }
}

impl<F: PrimeField + Ord, const W: usize>
    GateLayout<F, Vec<crate::circuitry::enforcement::Range<F>>> for VerticalGate<W>
{
    type Output = Vec<usize>;
    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<crate::circuitry::enforcement::Range<F>>,
    ) -> Result<Vec<usize>, Error> {
        let mut ranges: BTreeMap<usize, Vec<Witness<F>>> = BTreeMap::new();

        for range in e.iter() {
            ranges.entry(range.size).or_default().push(range.witness);
        }

        #[cfg(feature = "info")]
        {
            println!("---");
            let n = ranges.iter().fold(0, |acc, next| acc + next.1.len());
            println!("* n {n}");
            for (n_terms, witnesses) in ranges.iter() {
                println!("* size: {n_terms} occurs: {}", witnesses.len());
            }
        }

        let mut bit_sizes = BTreeSet::new();

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut crate::circuitry::RegionCtx::new(region, &mut ly_ctx.cell_map);

                ctx.empty(self.acc.into())?;
                for advice in self.advices.iter() {
                    ctx.empty((*advice).into())?;
                }
                ctx.empty(self.base.into())?;
                ctx.enable(self.eq_selector)?;
                ctx.next();

                for (limb_size, witnesses) in ranges.iter() {
                    bit_sizes.insert(*limb_size);

                    for chunk in witnesses.chunks(W) {
                        self.range_gate.enable(ctx, *limb_size)?;
                        ctx.empty(self.base.into())?;
                        ctx.empty(self.acc.into())?;
                        ctx.enable(self.eq_selector)?; // force acc to zero
                        for (witness, advice) in chunk.iter().zip(self.advices.iter()) {
                            let cell = ctx.advice(*advice, witness.value())?;
                            ctx.copy_chain(witness.id.expect("must be copiable"), cell)?;
                        }
                        ctx.next();

                        let chunk_len = chunk.len();
                        if chunk_len < W {
                            for i in chunk_len..W {
                                ctx.empty(self.advices[i].into())?;
                            }
                        }
                    }
                }

                Ok(ctx.offset())
            },
        )?;

        #[cfg(feature = "info")]
        {
            println!("* rows: {_offset}");
            println!();
        }

        let mut bit_sizes: Vec<_> = bit_sizes.iter().copied().collect();
        bit_sizes.sort();

        Ok(bit_sizes)
    }
}

impl<F: PrimeField + Ord, const W: usize>
    GateLayout<F, Vec<crate::circuitry::enforcement::RangeLimbs<F>>> for VerticalGate<W>
{
    type Output = Vec<usize>;

    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<crate::circuitry::enforcement::RangeLimbs<F>>,
    ) -> Result<Vec<usize>, Error> {
        let mut pow_of_twos: BTreeMap<usize, Vec<_>> = BTreeMap::new();

        let mut bases = |limb_size: usize| {
            macro_rules! div_ceil {
                ($a:expr, $b:expr) => {
                    (($a - 1) / $b) + 1
                };
            }
            pow_of_twos
                .entry(limb_size)
                .or_insert_with(|| {
                    (0..div_ceil!(F::NUM_BITS as usize, limb_size))
                        .map(|i| F::from(2).pow([(limb_size * i) as u64, 0, 0, 0]))
                        .collect()
                })
                .clone()
        };

        #[allow(clippy::type_complexity)]
        let mut compositions: BTreeMap<
            (usize, (usize, Option<usize>)),
            Vec<crate::circuitry::enforcement::RangeLimbs<_>>,
        > = BTreeMap::new();

        for composition in e.iter() {
            compositions
                .entry((
                    composition.limb_size,
                    (composition.limbs.len(), composition.overflow_size),
                ))
                .or_default()
                .push(composition.clone());
        }

        #[cfg(feature = "info")]
        {
            println!("---");

            let n = e.iter().map(|e| e.limbs.len()).sum::<usize>();
            println!("* n {n}");

            for ((limb_size, (n_limbs, overflow_size)), compositions) in compositions.iter() {
                println!(
                    "* size: {limb_size} nol: {n_limbs} occurs: {}, of: {:?}",
                    compositions.len(),
                    overflow_size,
                );
            }
        }

        let challenges = self
            .challenges
            .iter()
            .map(|challenge| ly_ctx.layouter.get_challenge(*challenge))
            .collect::<Vec<_>>();

        let mut bit_sizes = BTreeSet::new();

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut crate::circuitry::RegionCtx::new(region, &mut ly_ctx.cell_map);

                ctx.empty(self.acc.into())?;
                for advice in self.advices.iter() {
                    ctx.empty((*advice).into())?;
                }
                ctx.empty(self.base.into())?;
                ctx.enable(self.eq_selector)?;
                ctx.next();

                for ((limb_size, (n_limbs, overflow_size)), compositions) in compositions.iter() {
                    let bases = bases(*limb_size);

                    for chunk in compositions.chunks(W) {
                        let mut acc = Value::known(F::ZERO);
                        for (limb_idx, base) in bases.iter().take(*n_limbs).enumerate() {
                            let composition = chunk.first().unwrap();
                            let limb = composition.limbs[limb_idx].value();
                            ctx.advice(*self.advices.first().unwrap(), limb)?;
                            let mut row_rlc = limb;

                            let is_last = limb_idx == *n_limbs - 1;
                            let bit_size = is_last
                                .then_some(())
                                .and(*overflow_size)
                                .unwrap_or(*limb_size);
                            bit_sizes.insert(bit_size);
                            self.range_gate.enable(ctx, bit_size)?;

                            for ((composition, advice), challenge) in chunk
                                .iter()
                                .zip(self.advices.iter())
                                .skip(1)
                                .zip(challenges.iter())
                            {
                                let limb = composition.limbs[limb_idx].value();
                                ctx.advice(*advice, limb)?;
                                row_rlc = row_rlc + limb * challenge;

                                let bit_size = is_last
                                    .then_some(())
                                    .and(*overflow_size)
                                    .unwrap_or(*limb_size);

                                bit_sizes.insert(bit_size);
                                self.range_gate.enable(ctx, bit_size)?;
                            }

                            let chunk_len = chunk.len();
                            if chunk_len < W {
                                for i in chunk_len..W {
                                    ctx.empty(self.advices[i].into())?;
                                }
                            }

                            acc = row_rlc.map(|row_rlc| row_rlc * base) + acc;

                            ctx.enable(self.acc_selector)?;
                            ctx.fixed(self.base, *base)?;
                            ctx.advice(self.acc, acc)?;
                            ctx.next();
                        }

                        let composed = chunk.first().unwrap().composed;
                        let cell = ctx.advice(*self.advices.first().unwrap(), composed.value())?;
                        ctx.copy_chain(composed.id().expect("must be copiable"), cell)?;
                        let mut row_rlc = composed.value();

                        for ((composition, advice), challenge) in chunk
                            .iter()
                            .zip(self.advices.iter())
                            .skip(1)
                            .zip(challenges.iter())
                        {
                            let composed = composition.composed;
                            let cell = ctx.advice(*advice, composed.value())?;
                            ctx.copy_chain(composed.id.expect("must be copiable"), cell)?;
                            row_rlc = row_rlc + composed.value() * challenge;
                        }

                        let chunk_len = chunk.len();
                        if chunk_len < W {
                            for i in chunk_len..W {
                                ctx.empty(self.advices[i].into())?;
                            }
                        }

                        let acc = acc.zip(row_rlc).map(|(acc, row_rlc)| {
                            assert_eq!(acc, row_rlc);
                            F::ZERO
                        });

                        ctx.enable(self.eq_selector)?;
                        ctx.enable(self.acc_selector)?;
                        ctx.fixed(self.base, -F::ONE)?;
                        ctx.advice(self.acc, acc)?;

                        ctx.next();
                    }
                }

                Ok(ctx.offset())
            },
        )?;

        #[cfg(feature = "info")]
        {
            println!("* rows: {_offset}");
            println!();
        }

        let mut tables: Vec<_> = bit_sizes.iter().copied().collect();
        tables.sort();

        Ok(tables)
    }
}

impl<F: PrimeField + Ord> GateLayout<F, Vec<crate::circuitry::enforcement::FirstDegree<F>>>
    for VerticalGate<1>
{
    type Output = ();
    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        e: Vec<crate::circuitry::enforcement::FirstDegree<F>>,
    ) -> Result<(), Error> {
        #[cfg(feature = "info")]
        {
            let mut n: BTreeMap<usize, usize> = BTreeMap::new();

            for op in e.iter() {
                n.entry(op.terms.len())
                    .and_modify(|count| *count += 1)
                    .or_insert_with(|| 1);
            }

            println!("---");
            println!("vertical gate, first degree compositions");
            println!("* number of compositions: {}", e.len());
            for (n_terms, count) in n {
                println!("* n: {n_terms} occurs: {count}");
            }
        }

        let _offset = ly_ctx.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut crate::circuitry::RegionCtx::new(region, &mut ly_ctx.cell_map);
                let advice = *self.advices.first().unwrap();

                ctx.empty(self.acc.into())?;
                ctx.empty(advice.into())?;
                ctx.empty(self.base.into())?;
                ctx.next();

                for composition in e.iter() {
                    let constant = composition.constant;
                    assert_eq!(constant, F::ZERO, "no constant addition in vertical gate");

                    let n = composition.terms.len();
                    let mut acc = Value::known(F::ZERO);

                    // a0 | a0
                    // a1 | a0 + a1
                    // a2 | a0 + a1 + a2
                    // .. |
                    // a  | 0

                    // so that accumulator of next composition starts from zero!
                    assert!(!composition.terms.is_empty());

                    // this is an edge case that we exploit using as simple assignment
                    if composition.terms.len() == 1 {
                        let term = composition.terms.first().unwrap();
                        assert_eq!(term.factor, F::ONE);
                        let witness = term.witness;
                        // assign limb
                        let cell = ctx.advice(advice, witness.value())?;
                        // apply copy
                        ctx.copy_chain(witness.id.expect("must be copiable"), cell)?;

                        ctx.empty(self.base.into())?;
                        ctx.empty(self.acc.into())?;
                        ctx.enable(self.eq_selector)?;
                        ctx.next();
                        continue;
                    }

                    for (i, term) in composition.terms.iter().enumerate() {
                        let scale = term.factor;
                        let witness = term.witness;
                        let is_last = i == n - 1;
                        // if always open do we need it?
                        ctx.enable(self.acc_selector)?;

                        // assign limb
                        let cell = ctx.advice(advice, witness.value())?;
                        // apply copy
                        ctx.copy_chain(witness.id.expect("must be copiable"), cell)?;

                        // update accumulator
                        acc = acc.zip(term.value()).map(|(acc, term)| acc + term);
                        // assign accumulator
                        ctx.advice(self.acc, acc)?;

                        if is_last {
                            // expect zero at the last accumulator
                            ctx.enable(self.eq_selector)?;
                            assert_eq!(scale, -F::ONE, "don't scale the composition result");
                        }
                        // else {
                        //     // open range gate if needed
                        //     if let Some(range) = witness.range {
                        //         self.range_gate.enable(ctx, 0, range)?;
                        //     }
                        // }

                        // scale
                        ctx.fixed(self.base, scale)?;

                        // #[cfg(feature = "synth-sanity")]
                        // {
                        //     if is_last {
                        //         assert!(witness.range.is_none());
                        //     } else {
                        //         // assert!(witness.range.is_some());
                        //     }
                        // }

                        #[cfg(feature = "prover-sanity")]
                        {
                            if is_last {
                                acc.map(|acc| {
                                    assert_eq!(acc, F::ZERO);
                                });
                            }
                        }

                        ctx.next();
                    }
                }

                Ok(ctx.offset())
            },
        )?;

        #[cfg(feature = "info")]
        {
            println!("* rows: {_offset}");
            println!();
        }

        Ok(())
    }
}
