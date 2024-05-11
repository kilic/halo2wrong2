use super::{Fq2, PairingChip};
use crate::circuitry::{stack::Stack, witness::Witness};
use ff::PrimeField;
use halo2::{
    circuit::Value,
    halo2curves::bn256::{self, FROBENIUS_COEFF_FQ6_C1, FROBENIUS_COEFF_FQ6_C2},
};

#[derive(Clone, Debug)]
pub(crate) struct Fq6<N: PrimeField> {
    pub(crate) c0: Fq2<N>,
    pub(crate) c1: Fq2<N>,
    pub(crate) c2: Fq2<N>,
}

impl<N: PrimeField> Fq6<N> {
    pub fn value(&self) -> Value<bn256::Fq6> {
        self.c0
            .value()
            .zip(self.c1.value())
            .zip(self.c2.value())
            .map(|((c0, c1), c2)| bn256::Fq6 { c0, c1, c2 })
    }
}

impl<N: PrimeField + Ord> PairingChip<N> {
    pub(crate) fn fq6_one(&self, stack: &mut Stack<N>) -> Fq6<N> {
        Fq6 {
            c0: self.fq2_one(stack),
            c1: self.fq2_zero(stack),
            c2: self.fq2_zero(stack),
        }
    }

    pub(crate) fn fq6_zero(&self, stack: &mut Stack<N>) -> Fq6<N> {
        Fq6 {
            c0: self.fq2_zero(stack),
            c1: self.fq2_zero(stack),
            c2: self.fq2_zero(stack),
        }
    }

    pub(crate) fn fq6_assign(&self, stack: &mut Stack<N>, e: Value<bn256::Fq6>) -> Fq6<N> {
        Fq6 {
            c0: self.fq2_assign(stack, e.map(|e| e.c0)),
            c1: self.fq2_assign(stack, e.map(|e| e.c1)),
            c2: self.fq2_assign(stack, e.map(|e| e.c2)),
        }
    }

    pub(crate) fn fq6_constant(&self, stack: &mut Stack<N>, e: bn256::Fq6) -> Fq6<N> {
        Fq6 {
            c0: self.fq2_constant(stack, e.c0),
            c1: self.fq2_constant(stack, e.c1),
            c2: self.fq2_constant(stack, e.c2),
        }
    }

    pub(crate) fn fq6_select(
        &self,
        stack: &mut Stack<N>,
        a: &Fq6<N>,
        b: &Fq6<N>,
        cond: &Witness<N>,
    ) -> Fq6<N> {
        let c0 = self.fq2_select(stack, &a.c0, &b.c0, cond);
        let c1 = self.fq2_select(stack, &a.c1, &b.c1, cond);
        let c2 = self.fq2_select(stack, &a.c2, &b.c2, cond);
        Fq6 { c0, c1, c2 }
    }

    pub(crate) fn fq6_assert_zero(&self, stack: &mut Stack<N>, a: &Fq6<N>) {
        self.fq2_assert_zero(stack, &a.c0);
        self.fq2_assert_zero(stack, &a.c1);
        self.fq2_assert_zero(stack, &a.c2);
    }

    pub(crate) fn fq6_add(&self, stack: &mut Stack<N>, a: &Fq6<N>, b: &Fq6<N>) -> Fq6<N> {
        let c0 = self.fq2_add(stack, &a.c0, &b.c0);
        let c1 = self.fq2_add(stack, &a.c1, &b.c1);
        let c2 = self.fq2_add(stack, &a.c2, &b.c2);
        Fq6 { c0, c1, c2 }
    }

    pub(crate) fn fq6_double(&self, stack: &mut Stack<N>, a: &Fq6<N>) -> Fq6<N> {
        let c0 = self.fq2_double(stack, &a.c0);
        let c1 = self.fq2_double(stack, &a.c1);
        let c2 = self.fq2_double(stack, &a.c2);
        Fq6 { c0, c1, c2 }
    }

    pub(crate) fn fq6_sub(&self, stack: &mut Stack<N>, a: &Fq6<N>, b: &Fq6<N>) -> Fq6<N> {
        let c0 = self.fq2_sub(stack, &a.c0, &b.c0);
        let c1 = self.fq2_sub(stack, &a.c1, &b.c1);
        let c2 = self.fq2_sub(stack, &a.c2, &b.c2);
        Fq6 { c0, c1, c2 }
    }

    pub(crate) fn fq6_neg(&self, stack: &mut Stack<N>, a: &Fq6<N>) -> Fq6<N> {
        let c0 = self.fq2_neg(stack, &a.c0);
        let c1 = self.fq2_neg(stack, &a.c1);
        let c2 = self.fq2_neg(stack, &a.c2);
        Fq6 { c0, c1, c2 }
    }

    pub(crate) fn fq6_mul(&self, stack: &mut Stack<N>, a: &Fq6<N>, b: &Fq6<N>) -> Fq6<N> {
        let t0 = self.fq2_mul(stack, &a.c0, &b.c0);
        let t1 = self.fq2_mul(stack, &a.c1, &b.c1);
        let t2 = self.fq2_mul(stack, &a.c2, &b.c2);
        let t3 = self.fq2_add(stack, &a.c1, &a.c2);
        let t4 = self.fq2_add(stack, &b.c1, &b.c2);
        let t3 = self.fq2_mul(stack, &t3, &t4);
        let t4 = self.fq2_add(stack, &t1, &t2);
        let t3 = self.fq2_sub(stack, &t3, &t4);
        let t3 = self.fq2_mul_by_non_residue(stack, &t3);
        let t5 = self.fq2_add(stack, &t0, &t3);
        let t3 = self.fq2_add(stack, &a.c0, &a.c1);
        let t4 = self.fq2_add(stack, &b.c0, &b.c1);
        let t3 = self.fq2_mul(stack, &t3, &t4);
        let t4 = self.fq2_add(stack, &t0, &t1);
        let t3 = self.fq2_sub(stack, &t3, &t4);
        let t4 = self.fq2_mul_by_non_residue(stack, &t2);
        let c1 = self.fq2_add(stack, &t3, &t4);
        let t3 = self.fq2_add(stack, &a.c0, &a.c2);
        let t4 = self.fq2_add(stack, &b.c0, &b.c2);
        let t3 = self.fq2_mul(stack, &t3, &t4);
        let t4 = self.fq2_add(stack, &t0, &t2);
        let t3 = self.fq2_sub(stack, &t3, &t4);
        let c2 = self.fq2_add(stack, &t1, &t3);
        let c0 = t5;

        Fq6 { c0, c1, c2 }
    }

    pub(crate) fn fq6_mul_by_01(
        &self,
        stack: &mut Stack<N>,
        a: &Fq6<N>,
        c0: &Fq2<N>,
        c1: &Fq2<N>,
    ) -> Fq6<N> {
        let a_a = self.fq2_mul(stack, &a.c0, c0);
        let b_b = self.fq2_mul(stack, &a.c1, c1);
        let tmp = self.fq2_add(stack, &a.c1, &a.c2);
        let t1 = self.fq2_mul(stack, &tmp, c1);
        let t1 = self.fq2_sub(stack, &t1, &b_b);
        let t1 = self.fq2_mul_by_non_residue(stack, &t1);
        let t1 = self.fq2_add(stack, &t1, &a_a);
        let tmp = self.fq2_add(stack, &a.c0, &a.c2);
        let t3 = self.fq2_mul(stack, &tmp, c0);
        let t3 = self.fq2_sub(stack, &t3, &a_a);
        let t3 = self.fq2_add(stack, &t3, &b_b);
        let t2 = self.fq2_add(stack, c0, c1);
        let tmp = self.fq2_add(stack, &a.c0, &a.c1);
        let t2 = self.fq2_mul(stack, &tmp, &t2);
        let t2 = self.fq2_sub(stack, &t2, &a_a);
        let t2 = self.fq2_sub(stack, &t2, &b_b);

        Fq6 {
            c0: t1,
            c1: t2,
            c2: t3,
        }
    }

    pub(crate) fn fq6_mul_by_non_residue(&self, stack: &mut Stack<N>, a: &Fq6<N>) -> Fq6<N> {
        let t0 = self.fq2_mul_by_non_residue(stack, &a.c2);

        Fq6 {
            c0: t0,
            c1: a.c0.clone(),
            c2: a.c1.clone(),
        }
    }

    pub(crate) fn fq6_frobenius_map(
        &self,
        stack: &mut Stack<N>,
        a: &Fq6<N>,
        power: usize,
    ) -> Fq6<N> {
        let c0 = self.fq2_frobenius_map(stack, &a.c0, power);
        let c1 = self.fq2_frobenius_map(stack, &a.c1, power);
        let c2 = self.fq2_frobenius_map(stack, &a.c2, power);
        let fc1 = self.fq2_constant(stack, FROBENIUS_COEFF_FQ6_C1[power % 6]);
        let c1 = self.fq2_mul(stack, &c1, &fc1);
        let fc2 = self.fq2_constant(stack, FROBENIUS_COEFF_FQ6_C2[power % 6]);
        let c2 = self.fq2_mul(stack, &c2, &fc2);
        Fq6 { c0, c1, c2 }
    }
}
