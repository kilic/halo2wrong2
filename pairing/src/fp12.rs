use circuitry::stack::Stack;
use ff::PrimeField;
use halo2::halo2curves::bn256::FROBENIUS_COEFF_FQ12_C1;

use crate::{Fq12, Fq2, Fq6, PairingChip};

impl<
        N: PrimeField + Ord,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    > PairingChip<N, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>
{
    pub(crate) fn fq12_one(&self, stack: &mut Stack<N>) -> Fq12<N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        Fq12 {
            c0: self.fq6_one(stack),
            c1: self.fq6_zero(stack),
        }
    }

    pub(crate) fn fq12_conj(
        &self,
        stack: &mut Stack<N>,
        a: &Fq12<N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Fq12<N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let c0 = a.c0.clone();
        let c1 = self.fq6_neg(stack, &a.c1);
        Fq12 { c0, c1 }
    }

    pub(crate) fn fq12_mul(
        &self,
        stack: &mut Stack<N>,
        a: &Fq12<N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        b: &Fq12<N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Fq12<N, NUMBER_OF_LIMBS, LIMB_SIZE> {
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

    pub(crate) fn fq12_square(
        &self,
        stack: &mut Stack<N>,
        a: &Fq12<N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Fq12<N, NUMBER_OF_LIMBS, LIMB_SIZE> {
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

    pub(crate) fn fq12_mul_by_034(
        &self,
        stack: &mut Stack<N>,
        a: &Fq12<N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        c0: &Fq2<N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        c3: &Fq2<N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        c4: &Fq2<N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Fq12<N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let t0 = Fq6 {
            c0: self.fq2_mul(stack, &a.c0.c0, c0),
            c1: self.fq2_mul(stack, &a.c0.c1, c0),
            c2: self.fq2_mul(stack, &a.c0.c2, c0),
        };
        let t1 = self.fq6_mul_by_01(stack, &a.c1, c3, c4);
        let o = self.fq2_add(stack, c0, c3);
        let t2 = self.fq6_add(stack, &a.c0, &a.c1);
        let t2 = self.fq6_mul_by_01(stack, &t2, &o, c4);
        let t2 = self.fq6_sub(stack, &t2, &t0);
        let c1 = self.fq6_sub(stack, &t2, &t1);
        let t1 = self.fq6_mul_by_non_residue(stack, &t1);
        let c0 = self.fq6_add(stack, &t0, &t1);
        Fq12 { c0, c1 }
    }

    pub(crate) fn fq12_inverse(
        &self,
        stack: &mut Stack<N>,
        a: &Fq12<N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Fq12<N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let t0 = self.fq6_square(stack, &a.c0);
        let t1 = self.fq6_square(stack, &a.c1);
        let t1 = self.fq6_mul_by_non_residue(stack, &t1);
        let t1 = self.fq6_sub(stack, &t0, &t1);
        let t0 = self.fq6_inverse(stack, &t1);
        let c0 = self.fq6_mul(stack, &a.c0, &t0);
        let t0 = self.fq6_mul(stack, &t0, &a.c1);
        let c1 = self.fq6_neg(stack, &t0);
        Fq12 { c0, c1 }
    }

    pub(crate) fn fq12_frobenius_map(
        &self,
        stack: &mut Stack<N>,
        a: &Fq12<N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        power: usize,
    ) -> Fq12<N, NUMBER_OF_LIMBS, LIMB_SIZE> {
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

    fn fq4_square(
        &self,
        stack: &mut Stack<N>,

        a0: &Fq2<N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        a1: &Fq2<N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> (
        Fq2<N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        Fq2<N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        let t0 = self.fq2_square(stack, a0);
        let t1 = self.fq2_square(stack, a1);
        let t2 = self.fq2_mul_by_non_residue(stack, &t1);
        let c0 = self.fq2_add(stack, &t0, &t2);
        let t2 = self.fq2_add(stack, a0, a1);
        let t2 = self.fq2_square(stack, &t2);
        let t2 = self.fq2_sub(stack, &t2, &t0);
        let c1 = self.fq2_sub(stack, &t2, &t1);
        (c0, c1)
    }

    pub(crate) fn cyclotomic_square(
        &self,
        stack: &mut Stack<N>,
        a: &Fq12<N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Fq12<N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let (t3, t4) = self.fq4_square(stack, &a.c0.c0, &a.c1.c1);
        let t2 = self.fq2_sub(stack, &t3, &a.c0.c0);
        let t2 = self.fq2_double(stack, &t2);
        let c00 = self.fq2_add(stack, &t2, &t3);
        let t2 = self.fq2_add(stack, &t4, &a.c1.c1);
        let t2 = self.fq2_double(stack, &t2);
        let c11 = self.fq2_add(stack, &t2, &t4);
        let (t3, t4) = self.fq4_square(stack, &a.c1.c0, &a.c0.c2);
        let (t5, t6) = self.fq4_square(stack, &a.c0.c1, &a.c1.c2);
        let t2 = self.fq2_sub(stack, &t3, &a.c0.c1);
        let t2 = self.fq2_double(stack, &t2);
        let c01 = self.fq2_add(stack, &t2, &t3);
        let t2 = self.fq2_add(stack, &t4, &a.c1.c2);
        let t2 = self.fq2_double(stack, &t2);
        let c12 = self.fq2_add(stack, &t2, &t4);
        let t3 = self.fq2_mul_by_non_residue(stack, &t6);
        let t2 = self.fq2_add(stack, &t3, &a.c1.c0);
        let t2 = self.fq2_double(stack, &t2);
        let c10 = self.fq2_add(stack, &t2, &t3);
        let t2 = self.fq2_sub(stack, &t5, &a.c0.c2);
        let t2 = self.fq2_double(stack, &t2);
        let c02 = self.fq2_add(stack, &t2, &t5);

        let c0 = Fq6 {
            c0: c00,
            c1: c01,
            c2: c02,
        };
        let c1 = Fq6 {
            c0: c10,
            c1: c11,
            c2: c12,
        };
        Fq12 { c0, c1 }
    }
}
