use circuitry::stack::Stack;
use ff::{Field, PrimeField};
use halo2::halo2curves::{bn256::Fq, bn256::Fq2 as ConstantFq2};
use integer::integer::Integer;

use crate::{Fq2, PairingChip};

impl<N: PrimeField + Ord> PairingChip<N> {
    pub(crate) fn fq2_add(&self, stack: &mut Stack<N>, a: &Fq2<N>, b: &Fq2<N>) -> Fq2<N> {
        Fq2 {
            c0: self.ch.add(stack, &a.c0, &b.c0),
            c1: self.ch.add(stack, &a.c1, &b.c1),
        }
    }

    pub(crate) fn fq2_normal_equal(&self, stack: &mut Stack<N>, a: &Fq2<N>, b: &Fq2<N>) {
        self.ch.normal_equal(stack, &a.c0, &b.c0);
        self.ch.normal_equal(stack, &a.c1, &b.c1);
    }

    pub(crate) fn fq2_mul_by_fq(
        &self,
        stack: &mut Stack<N>,
        a: &Fq2<N>,
        b: &Integer<Fq, N>,
    ) -> Fq2<N> {
        Fq2 {
            c0: self.ch.mul(stack, &a.c0, b, &[]),
            c1: self.ch.mul(stack, &a.c1, b, &[]),
        }
    }

    pub(crate) fn fq2_one(&self, stack: &mut Stack<N>) -> Fq2<N> {
        let one = self.ch.register_constant(stack, &Fq::ONE);
        let zero = self.ch.register_constant(stack, &Fq::ZERO);
        Fq2 {
            c0: one.clone(),
            c1: zero.clone(),
        }
    }

    pub(crate) fn fq2_zero(&self, stack: &mut Stack<N>) -> Fq2<N> {
        let zero = self.ch.register_constant(stack, &Fq::ZERO);
        Fq2 {
            c0: zero.clone(),
            c1: zero.clone(),
        }
    }

    pub(crate) fn fq2_constant(&self, stack: &mut Stack<N>, constant: ConstantFq2) -> Fq2<N> {
        let c0 = self.ch.register_constant(stack, &constant.c0);
        let c1 = self.ch.register_constant(stack, &constant.c1);
        Fq2 { c0, c1 }
    }

    pub(crate) fn fq2_double(&self, stack: &mut Stack<N>, a: &Fq2<N>) -> Fq2<N> {
        Fq2 {
            c0: self.ch.add(stack, &a.c0, &a.c0),
            c1: self.ch.add(stack, &a.c1, &a.c1),
        }
    }

    pub(crate) fn fq2_sub(&self, stack: &mut Stack<N>, a: &Fq2<N>, b: &Fq2<N>) -> Fq2<N> {
        Fq2 {
            c0: self.ch.sub(stack, &a.c0, &b.c0),
            c1: self.ch.sub(stack, &a.c1, &b.c1),
        }
    }

    pub(crate) fn fq2_neg(&self, stack: &mut Stack<N>, a: &Fq2<N>) -> Fq2<N> {
        Fq2 {
            c0: self.ch.neg(stack, &a.c0),
            c1: self.ch.neg(stack, &a.c1),
        }
    }

    pub(crate) fn fq2_conj(&self, stack: &mut Stack<N>, a: &Fq2<N>) -> Fq2<N> {
        Fq2 {
            c0: a.c0.clone(),
            c1: self.ch.neg(stack, &a.c1),
        }
    }

    pub(crate) fn fq2_mul(&self, stack: &mut Stack<N>, a: &Fq2<N>, b: &Fq2<N>) -> Fq2<N> {
        let t1 = self.ch.mul(stack, &a.c0, &b.c0, &[]);
        let t2 = self.ch.mul(stack, &a.c1, &b.c1, &[]);
        let t0 = self.ch.add(stack, &a.c0, &a.c1);
        let t3 = self.ch.add(stack, &b.c0, &b.c1);
        let c0 = self.ch.sub(stack, &t1, &t2);
        let t1 = self.ch.add(stack, &t1, &t2);
        let t0 = self.ch.mul(stack, &t0, &t3, &[]);
        let c1 = self.ch.sub(stack, &t0, &t1);
        Fq2 { c0, c1 }
    }

    pub(crate) fn fq2_square(&self, stack: &mut Stack<N>, a: &Fq2<N>) -> Fq2<N> {
        let t0 = self.ch.add(stack, &a.c0, &a.c1);
        let t1 = self.ch.sub(stack, &a.c0, &a.c1);
        let t2 = self.ch.add(stack, &a.c0, &a.c0);
        let c0 = self.ch.mul(stack, &t0, &t1, &[]);
        let c1 = self.ch.mul(stack, &t2, &a.c1, &[]);
        Fq2 { c0, c1 }
    }

    pub(crate) fn fq2_mul_by_non_residue(&self, stack: &mut Stack<N>, a: &Fq2<N>) -> Fq2<N> {
        let t0 = self.ch.double(stack, &a.c1);
        let t0 = self.ch.double(stack, &t0);
        let t0 = self.ch.double(stack, &t0);
        let t0 = self.ch.add(stack, &t0, &a.c1);
        let t0 = self.ch.add(stack, &t0, &a.c0);
        let t1 = self.ch.double(stack, &a.c0);
        let t1 = self.ch.double(stack, &t1);
        let t1 = self.ch.double(stack, &t1);
        let t1 = self.ch.add(stack, &t1, &a.c0);
        let t1 = self.ch.sub(stack, &t1, &a.c1);

        Fq2 { c0: t1, c1: t0 }
    }

    // pub(crate) fn fq2_mul_by_b(
    //     &self,
    //     stack: &mut Stack<N>,
    //     a: &Fq2<N, >,
    // ) -> Fq2<N, > {
    //     let t0 = self.ch.add(stack, &a.c0, &a.c0);
    //     let t1 = self.ch.add(stack, &a.c1, &a.c1);
    //     let t0 = self.ch.add(stack, &t0, &t0);
    //     let t1 = self.ch.add(stack, &t1, &t1);
    //     let c0 = self.ch.sub(stack, &t0, &t1);
    //     let c1 = self.ch.add(stack, &t0, &t1);
    //     Fq2 { c0, c1 }
    // }

    pub(crate) fn fq2_inverse(&self, stack: &mut Stack<N>, a: &Fq2<N>) -> Fq2<N> {
        let t0 = self.ch.square(stack, &a.c0, &[]);
        let t1 = self.ch.square(stack, &a.c1, &[]);
        let t0 = self.ch.add(stack, &t0, &t1);
        let c0 = self.ch.div(stack, &a.c0, &t0);
        let t0 = self.ch.div(stack, &a.c1, &t0);
        let c1 = self.ch.neg(stack, &t0);
        Fq2 { c0, c1 }
    }

    pub(crate) fn fq2_frobenius_map(
        &self,
        stack: &mut Stack<N>,
        a: &Fq2<N>,
        power: usize,
    ) -> Fq2<N> {
        if power % 2 != 0 {
            self.fq2_conj(stack, a)
        } else {
            a.clone()
        }
    }
}
