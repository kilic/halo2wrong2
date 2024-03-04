use crate::{Fq2, Fq6, PairingChip};
use circuitry::stack::Stack;
use ff::PrimeField;
use halo2::halo2curves::bn256::{FROBENIUS_COEFF_FQ6_C1, FROBENIUS_COEFF_FQ6_C2};

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

    pub(crate) fn fq6_square(&self, stack: &mut Stack<N>, a: &Fq6<N>) -> Fq6<N> {
        let s0 = self.fq2_square(stack, &a.c0);
        let ab = self.fq2_mul(stack, &a.c0, &a.c1);
        let s1 = self.fq2_double(stack, &ab);
        let s2 = self.fq2_sub(stack, &a.c0, &a.c1);
        let s2 = self.fq2_add(stack, &s2, &a.c2);
        let s2 = self.fq2_square(stack, &s2);
        let bc = self.fq2_mul(stack, &a.c1, &a.c2);
        let s3 = self.fq2_double(stack, &bc);
        let s4 = self.fq2_square(stack, &a.c2);
        let c0 = self.fq2_mul_by_non_residue(stack, &s3);
        let c0 = self.fq2_add(stack, &c0, &s0);
        let c1 = self.fq2_mul_by_non_residue(stack, &s4);
        let c1 = self.fq2_add(stack, &c1, &s1);
        let c2 = self.fq2_add(stack, &s1, &s2);
        let c2 = self.fq2_add(stack, &c2, &s3);
        let c2 = self.fq2_sub(stack, &c2, &s0);
        let c2 = self.fq2_sub(stack, &c2, &s4);

        Fq6 { c0, c1, c2 }
    }

    pub(crate) fn fq6_mul_by_non_residue(&self, stack: &mut Stack<N>, a: &Fq6<N>) -> Fq6<N> {
        let t0 = self.fq2_mul_by_non_residue(stack, &a.c2);

        Fq6 {
            c0: t0,
            c1: a.c0.clone(),
            c2: a.c1.clone(),
        }
    }

    pub(crate) fn fq6_inverse(&self, stack: &mut Stack<N>, a: &Fq6<N>) -> Fq6<N> {
        let t0 = self.fq2_square(stack, &a.c0);
        let t1 = self.fq2_mul(stack, &a.c1, &a.c2);
        let t1 = self.fq2_mul_by_non_residue(stack, &t1);
        let t0 = self.fq2_sub(stack, &t0, &t1);
        let t1 = self.fq2_square(stack, &a.c1);
        let t2 = self.fq2_mul(stack, &a.c0, &a.c2);
        let t1 = self.fq2_sub(stack, &t1, &t2);
        let t2 = self.fq2_square(stack, &a.c2);
        let t2 = self.fq2_mul_by_non_residue(stack, &t2);
        let t3 = self.fq2_mul(stack, &a.c0, &a.c1);
        let t2 = self.fq2_sub(stack, &t2, &t3);
        let t3 = self.fq2_mul(stack, &a.c2, &t2);
        let t4 = self.fq2_mul(stack, &a.c1, &t1);
        let t3 = self.fq2_add(stack, &t3, &t4);
        let t3 = self.fq2_mul_by_non_residue(stack, &t3);
        let t4 = self.fq2_mul(stack, &a.c0, &t0);
        let t3 = self.fq2_add(stack, &t3, &t4);
        let t3 = self.fq2_inverse(stack, &t3);
        let c0 = self.fq2_mul(stack, &t0, &t3);
        let c1 = self.fq2_mul(stack, &t2, &t3);
        let c2 = self.fq2_mul(stack, &t1, &t3);

        Fq6 { c0, c1, c2 }
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
