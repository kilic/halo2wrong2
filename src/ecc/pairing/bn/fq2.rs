use crate::circuitry::{stack::Stack, witness::Witness};
use crate::ecc::pairing::bn::BNPairingChip;
use crate::integer::{Integer, Range};
use ff::{Field, PrimeField};
use halo2::{circuit::Value, halo2curves::bn256};

#[derive(Clone, Debug)]
pub struct Fq2<N: PrimeField> {
    c0: Integer<bn256::Fq, N>,
    c1: Integer<bn256::Fq, N>,
}

impl<N: PrimeField> Fq2<N> {
    pub fn value(&self) -> Value<bn256::Fq2> {
        self.c0
            .value()
            .zip(self.c1.value())
            .map(|(c0, c1)| bn256::Fq2::new(c0, c1))
    }
}

impl<N: PrimeField + Ord> BNPairingChip<N> {
    pub fn fq2_assign(
        &self,
        stack: &mut Stack<N>,
        e: Value<halo2::halo2curves::bn256::Fq2>,
    ) -> Fq2<N> {
        let e = e.map(|e| (e.c0, e.c1));
        let c0 = e.map(|e| e.0);
        let c0 = self.ch.rns().unassigned(c0);
        let c0 = self.ch.assign(stack, c0, Range::Remainder);
        let c1 = e.map(|e| e.1);
        let c1 = self.ch.rns().unassigned(c1);
        let c1 = self.ch.assign(stack, c1, Range::Remainder);
        Fq2 { c0, c1 }
    }

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

    pub(crate) fn fq2_assert_zero(&self, stack: &mut Stack<N>, a: &Fq2<N>) {
        self.ch.assert_zero(stack, &a.c0);
        self.ch.assert_zero(stack, &a.c1);
    }

    pub(crate) fn fq2_select(
        &self,
        stack: &mut Stack<N>,
        a: &Fq2<N>,
        b: &Fq2<N>,
        cond: &Witness<N>,
    ) -> Fq2<N> {
        let c0 = self.ch.select(stack, &a.c0, &b.c0, cond);
        let c1 = self.ch.select(stack, &a.c1, &b.c1, cond);
        Fq2 { c0, c1 }
    }

    pub(crate) fn fq2_reduce(&self, stack: &mut Stack<N>, a: &Fq2<N>) -> Fq2<N> {
        Fq2 {
            c0: self.ch.reduce(stack, &a.c0),
            c1: self.ch.reduce(stack, &a.c1),
        }
    }

    pub(crate) fn fq2_mul_by_fq(
        &self,
        stack: &mut Stack<N>,
        a: &Fq2<N>,
        b: &Integer<bn256::Fq, N>,
    ) -> Fq2<N> {
        Fq2 {
            c0: self.ch.mul(stack, &a.c0, b, &[]),
            c1: self.ch.mul(stack, &a.c1, b, &[]),
        }
    }

    pub(crate) fn fq2_mul_by_fq_constant(
        &self,
        stack: &mut Stack<N>,
        a: &bn256::Fq2,
        b: &Integer<bn256::Fq, N>,
    ) -> Fq2<N> {
        Fq2 {
            c0: self
                .ch
                .mul_constant(stack, b, &self.ch.rns().constant(&a.c0), &[]),
            c1: self
                .ch
                .mul_constant(stack, b, &self.ch.rns().constant(&a.c1), &[]),
        }
    }

    pub(crate) fn fq2_one(&self, stack: &mut Stack<N>) -> Fq2<N> {
        let one = self.ch.register_constant(stack, &bn256::Fq::ONE);
        let zero = self.ch.register_constant(stack, &bn256::Fq::ZERO);
        Fq2 {
            c0: one.clone(),
            c1: zero.clone(),
        }
    }

    pub(crate) fn fq2_zero(&self, stack: &mut Stack<N>) -> Fq2<N> {
        let zero = self.ch.register_constant(stack, &bn256::Fq::ZERO);
        Fq2 {
            c0: zero.clone(),
            c1: zero.clone(),
        }
    }

    pub(crate) fn fq2_constant(&self, stack: &mut Stack<N>, constant: bn256::Fq2) -> Fq2<N> {
        let c0 = self.ch.register_constant(stack, &constant.c0);
        let c1 = self.ch.register_constant(stack, &constant.c1);
        Fq2 { c0, c1 }
    }

    pub(crate) fn fq2_double(&self, stack: &mut Stack<N>, a: &Fq2<N>) -> Fq2<N> {
        Fq2 {
            c0: self.ch.double(stack, &a.c0),
            c1: self.ch.double(stack, &a.c1),
        }
    }

    pub(crate) fn fq2_mul3(&self, stack: &mut Stack<N>, a: &Fq2<N>) -> Fq2<N> {
        Fq2 {
            c0: self.ch.mul3(stack, &a.c0),
            c1: self.ch.mul3(stack, &a.c1),
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

    // pub(crate) fn fq2_mul_constant(
    //     &self,
    //     stack: &mut Stack<N>,
    //     a: &Fq2<N>,
    //     b: &bn256::Fq2,
    // ) -> Fq2<N> {
    //     let t1 = self
    //         .ch
    //         .mul_constant(stack, &a.c0, &self.ch.rns().constant(&b.c0), &[]);
    //     let t2 = self
    //         .ch
    //         .mul_constant(stack, &a.c1, &self.ch.rns().constant(&b.c1), &[]);
    //     let t0 = self.ch.add(stack, &a.c0, &a.c1);
    //     let t3 = b.c0 + b.c1;

    //     let c0 = self.ch.sub(stack, &t1, &t2);
    //     let t1 = self.ch.add(stack, &t1, &t2);
    //     let t0 = self
    //         .ch
    //         .mul_constant(stack, &t0, &self.ch.rns().constant(&t3), &[]);
    //     let c1 = self.ch.sub(stack, &t0, &t1);
    //     Fq2 { c0, c1 }
    // }

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

    // pub(crate) fn fq2_inverse(&self, stack: &mut Stack<N>, a: &Fq2<N>) -> Fq2<N> {
    //     let t0 = self.ch.square(stack, &a.c0, &[]);
    //     let t1 = self.ch.square(stack, &a.c1, &[]);
    //     let t0 = self.ch.add(stack, &t0, &t1);
    //     let c0 = self.ch.div(stack, &a.c0, &t0);
    //     let t0 = self.ch.div(stack, &a.c1, &t0);
    //     let c1 = self.ch.neg(stack, &t0);
    //     Fq2 { c0, c1 }
    // }

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
