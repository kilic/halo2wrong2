use super::{fq6::Fq6, Fq2, PairingChip};
use crate::circuitry::{stack::Stack, witness::Witness};
use ff::PrimeField;
use halo2::{
    circuit::Value,
    halo2curves::bn256::{self, FROBENIUS_COEFF_FQ12_C1},
};

#[derive(Clone, Debug)]
pub struct Fq12<N: PrimeField> {
    c0: Fq6<N>,
    c1: Fq6<N>,
}

impl<N: PrimeField> Fq12<N> {
    pub fn value(&self) -> Value<bn256::Fq12> {
        self.c0
            .value()
            .zip(self.c1.value())
            .map(|(c0, c1)| bn256::Fq12 { c0, c1 })
    }
}

impl<N: PrimeField + Ord> PairingChip<N> {
    pub(crate) fn fq12_one(&self, stack: &mut Stack<N>) -> Fq12<N> {
        Fq12 {
            c0: self.fq6_one(stack),
            c1: self.fq6_zero(stack),
        }
    }

    pub(crate) fn fq12_constant(&self, stack: &mut Stack<N>, e: bn256::Fq12) -> Fq12<N> {
        Fq12 {
            c0: self.fq6_constant(stack, e.c0),
            c1: self.fq6_constant(stack, e.c1),
        }
    }

    pub(crate) fn fq12_sub(&self, stack: &mut Stack<N>, a: &Fq12<N>, b: &Fq12<N>) -> Fq12<N> {
        let c0 = self.fq6_sub(stack, &a.c0, &b.c0);
        let c1 = self.fq6_sub(stack, &a.c1, &b.c1);
        Fq12 { c0, c1 }
    }

    pub(crate) fn fq12_assign(&self, stack: &mut Stack<N>, e: Value<bn256::Fq12>) -> Fq12<N> {
        Fq12 {
            c0: self.fq6_assign(stack, e.map(|e| e.c0)),
            c1: self.fq6_assign(stack, e.map(|e| e.c1)),
        }
    }

    pub(crate) fn fq12_select(
        &self,
        stack: &mut Stack<N>,
        a: &Fq12<N>,
        b: &Fq12<N>,
        cond: &Witness<N>,
    ) -> Fq12<N> {
        let c0 = self.fq6_select(stack, &a.c0, &b.c0, cond);
        let c1 = self.fq6_select(stack, &a.c1, &b.c1, cond);
        Fq12 { c0, c1 }
    }

    pub(crate) fn fq12_mul(&self, stack: &mut Stack<N>, a: &Fq12<N>, b: &Fq12<N>) -> Fq12<N> {
        let t = self.fq6_mul(stack, &a.c0, &b.c0);
        let t1 = self.fq6_mul(stack, &a.c1, &b.c1);
        let t2 = self.fq6_add(stack, &b.c0, &b.c1);
        let c1 = self.fq6_add(stack, &a.c1, &a.c0);
        let c1 = self.fq6_mul(stack, &c1, &t2);
        let c1 = self.fq6_sub(stack, &c1, &t);
        let c1 = self.fq6_sub(stack, &c1, &t1);
        let t1 = self.fq6_mul_by_non_residue(stack, &t1);
        let c0 = self.fq6_add(stack, &t, &t1);
        Fq12 { c0, c1 }
    }

    pub(crate) fn fq12_square(&self, stack: &mut Stack<N>, a: &Fq12<N>) -> Fq12<N> {
        let t0 = self.fq6_add(stack, &a.c0, &a.c1);
        let t2 = self.fq6_mul(stack, &a.c0, &a.c1);
        let t1 = self.fq6_mul_by_non_residue(stack, &a.c1);
        let t1 = self.fq6_add(stack, &t1, &a.c0);
        let t3 = self.fq6_mul_by_non_residue(stack, &t2);
        let t0 = self.fq6_mul(stack, &t0, &t1);
        let t0 = self.fq6_sub(stack, &t0, &t2);
        let c0 = self.fq6_sub(stack, &t0, &t3);
        let c1 = self.fq6_double(stack, &t2);
        Fq12 { c0, c1 }
    }

    pub(crate) fn fq12_mul_sparse(
        &self,
        stack: &mut Stack<N>,
        f: &mut Fq12<N>,

        c3: &Fq2<N>,
        c4: &Fq2<N>,
    ) {
        let t = self.fq6_mul_by_01(stack, &f.c1, c3, c4);
        let t = self.fq6_mul_by_non_residue(stack, &t);
        let c0 = self.fq6_add(stack, &f.c0, &t);

        let t = self.fq6_mul_by_01(stack, &f.c0, c3, c4);
        let c1 = self.fq6_add(stack, &f.c1, &t);

        f.c0 = c0;
        f.c1 = c1;
    }

    pub(crate) fn fq12_frobenius_map(
        &self,
        stack: &mut Stack<N>,
        a: &Fq12<N>,
        power: usize,
    ) -> Fq12<N> {
        let c0 = self.fq6_frobenius_map(stack, &a.c0, power);
        let c1 = self.fq6_frobenius_map(stack, &a.c1, power);

        match power {
            0 => Fq12 { c0, c1 },
            6 => {
                let c1 = self.fq6_neg(stack, &c1);
                Fq12 { c0, c1 }
            }
            _ => {
                let e = self.fq2_constant(stack, FROBENIUS_COEFF_FQ12_C1[power]);
                let u0 = self.fq2_mul(stack, &c1.c0, &e);
                let u1 = self.fq2_mul(stack, &c1.c1, &e);
                let u2 = self.fq2_mul(stack, &c1.c2, &e);
                let c1 = Fq6 {
                    c0: u0,
                    c1: u1,
                    c2: u2,
                };
                Fq12 { c0, c1 }
            }
        }
    }

    pub(crate) fn fq12_assert_zero(&self, stack: &mut Stack<N>, a: &Fq12<N>) {
        self.fq6_assert_zero(stack, &a.c0);
        self.fq6_assert_zero(stack, &a.c1);
    }

    pub(crate) fn fq12_inverse(&self, stack: &mut Stack<N>, e: &Fq12<N>) -> Fq12<N> {
        let inv_e = e.value().map(|e| e.invert().unwrap());
        let inv_e = self.fq12_assign(stack, inv_e);
        let must_be_one = self.fq12_mul(stack, e, &inv_e);
        let one = self.fq12_one(stack);
        let must_be_zero = self.fq12_sub(stack, &must_be_one, &one);
        self.fq12_assert_zero(stack, &must_be_zero);

        inv_e
    }
}
