use circuitry::{chip::second_degree::SecondDegreeChip, stack::Stack, witness::Witness};
use ecc::Point;
use ff::{Field, PrimeField};
use halo2::{
    circuit::Value,
    halo2curves::{
        bn256::{G1Affine, G2Affine, FROBENIUS_COEFF_FQ6_C1, XI_TO_Q_MINUS_1_OVER_2},
        CurveAffine,
    },
};
use integer::{
    chip::IntegerChip,
    integer::{Integer, Range},
    rns::Rns,
};

use halo2::halo2curves::bn256::Fq;

mod fp12;
mod fp2;
mod fp6;
#[cfg(test)]
mod test;

pub const SIX_U_PLUS_2_NAF: [i8; 65] = [
    0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0,
    1, 1, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0,
    0, 1, 0, 1, 1,
];

#[derive(Clone, Debug)]
pub struct Fq2<N: PrimeField> {
    c0: Integer<Fq, N>,
    c1: Integer<Fq, N>,
}

#[derive(Clone, Debug)]
struct Fq6<N: PrimeField> {
    c0: Fq2<N>,
    c1: Fq2<N>,
    c2: Fq2<N>,
}

#[derive(Clone, Debug)]
pub struct Fq12<N: PrimeField> {
    c0: Fq6<N>,
    c1: Fq6<N>,
}

#[derive(Clone, Debug)]
pub struct Point2Affine<N: PrimeField> {
    x: Fq2<N>,
    y: Fq2<N>,
}

#[derive(Clone, Debug)]
pub struct Point2<N: PrimeField> {
    x: Fq2<N>,
    y: Fq2<N>,
    z: Fq2<N>,
}

#[derive(Debug, Clone)]
pub struct PairingChip<N: PrimeField + Ord> {
    pub ch: IntegerChip<Fq, N>,
}

impl<N: PrimeField + Ord> PairingChip<N> {
    pub fn new(rns: &Rns<Fq, N>, sublimb_size: usize) -> Self {
        let ch = IntegerChip::new(rns, sublimb_size);
        Self { ch }
    }

    pub fn assign_fq2(
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

    pub fn assert_on_curve2(&self, stack: &mut Stack<N>, point: &Point2Affine<N>) {
        let y_square = &self.fq2_square(stack, &point.y);
        let x_square = &self.fq2_square(stack, &point.x);
        let x_cube = &self.fq2_mul(stack, &point.x, x_square);
        let b = self.fq2_constant(stack, G2Affine::b());
        let x_cube_b = &self.fq2_add(stack, x_cube, &b);
        self.fq2_normal_equal(stack, x_cube_b, y_square);
    }

    pub fn assign_point2(&self, stack: &mut Stack<N>, point: Value<G2Affine>) -> Point2Affine<N> {
        let coordinates = point.map(|point| {
            let coordinates = point.coordinates().unwrap();
            (*coordinates.x(), *coordinates.y())
        });
        let x = coordinates.map(|coordinates| coordinates.0);
        let x = self.assign_fq2(stack, x);
        let y = coordinates.map(|coordinates| coordinates.1);
        let y = self.assign_fq2(stack, y);

        let point = Point2Affine { x, y };

        self.assert_on_curve2(stack, &point);
        point
    }

    pub fn assert_on_curve1(&self, stack: &mut Stack<N>, point: &Point<Fq, N>) {
        let y_square = &self.ch.square(stack, point.y(), &[]);
        let x_square = &self.ch.square(stack, point.x(), &[]);
        let x_cube = &self.ch.mul(stack, point.x(), x_square, &[]);
        let b = self.ch.rns().constant(&G1Affine::b());

        let x_cube_b = &self.ch.add_constant(stack, x_cube, &b);
        self.ch.normal_equal(stack, x_cube_b, y_square);
    }

    pub fn assign_point1(
        &self,
        stack: &mut Stack<N>,
        point: Value<G1Affine>,
    ) -> Point<halo2::halo2curves::bn256::Fq, N> {
        let (x, y) = point
            .map(|point| {
                let coords = point.coordinates();
                // disallow point of infinity
                // it will not pass assing point enforcement
                let coords = coords.unwrap();
                let x = coords.x();
                let y = coords.y();
                (*x, *y)
            })
            .unzip();

        let x = &self
            .ch
            .range(stack, &self.ch.rns().unassigned(x), Range::Remainder);
        let y = &self
            .ch
            .range(stack, &self.ch.rns().unassigned(y), Range::Remainder);

        let point = Point::new(x, y);
        self.assert_on_curve1(stack, &point);

        point
    }

    fn miller_loop(
        &self,
        stack: &mut Stack<N>,
        f: &mut Fq12<N>,
        g1: Vec<Point<Fq, N>>,
        g2: Vec<Point2Affine<N>>,
    ) {
        // TODO: infinity points?
        // in aggregation context we can just disallow
        // but in precompile context we
        let mut r = g2
            .iter()
            .map(|g2| {
                let z = self.fq2_constant(stack, halo2::halo2curves::bn256::Fq2::ONE);
                Point2 {
                    x: g2.x.clone(),
                    y: g2.y.clone(),
                    z,
                }
            })
            .collect::<Vec<_>>();

        for (i, x) in SIX_U_PLUS_2_NAF.iter().rev().skip(1).enumerate() {
            // println!("loop = {:#?}", f);

            if i != 0 {
                *f = self.fq12_square(stack, f);
            }

            g1.iter()
                .zip(g2.iter())
                .zip(r.iter_mut())
                .for_each(|((g1, _), r)| self.double(stack, f, r, g1));

            match x {
                1 => {
                    g1.iter()
                        .zip(g2.iter())
                        .zip(r.iter_mut())
                        .for_each(|((g1, g2), r)| self.add(stack, f, r, g2, g1));
                }
                -1 => {
                    g1.iter()
                        .zip(g2.iter())
                        .zip(r.iter_mut())
                        .for_each(|((g1, g2), r)| {
                            let mut g2 = g2.clone();
                            g2.y = self.fq2_neg(stack, &g2.y);
                            self.add(stack, f, r, &g2, g1);
                        });
                }
                _ => {}
            }
        }

        g1.iter()
            .zip(g2.iter())
            .zip(r.iter_mut())
            .for_each(|((g1, g2), r)| {
                let mut g2 = g2.clone();
                g2.x = self.fq2_conj(stack, &g2.x);
                let e = self.fq2_constant(stack, FROBENIUS_COEFF_FQ6_C1[1]);
                g2.x = self.fq2_mul(stack, &g2.x, &e);
                g2.y = self.fq2_conj(stack, &g2.y);
                let e = self.fq2_constant(stack, XI_TO_Q_MINUS_1_OVER_2);
                g2.y = self.fq2_mul(stack, &g2.y, &e);
                self.add(stack, f, r, &g2, g1)
            });

        g1.iter()
            .zip(g2.iter())
            .zip(r.iter_mut())
            .for_each(|((g1, g2), r)| {
                let mut g2 = g2.clone();
                let e = self.fq2_constant(stack, FROBENIUS_COEFF_FQ6_C1[2]);
                g2.x = self.fq2_mul(stack, &g2.x, &e);
                self.add(stack, f, r, &g2, g1)
            });
    }

    fn double(&self, stack: &mut Stack<N>, f: &mut Fq12<N>, r: &mut Point2<N>, g1: &Point<Fq, N>) {
        let t0 = self.fq2_square(stack, &r.x);
        let t1 = self.fq2_square(stack, &r.y);
        let t2 = self.fq2_square(stack, &t1);
        let t3 = self.fq2_add(stack, &r.x, &t1);
        let t3 = self.fq2_square(stack, &t3);
        let t3 = self.fq2_sub(stack, &t3, &t0);
        let t3 = self.fq2_sub(stack, &t3, &t2);
        let t3 = self.fq2_double(stack, &t3);
        let t4 = self.fq2_double(stack, &t0);
        let t4 = self.fq2_add(stack, &t4, &t0);
        let t5 = self.fq2_square(stack, &t4);
        let t6 = self.fq2_add(stack, &r.x, &t4);
        let zsquared = self.fq2_square(stack, &r.z);
        r.x = self.fq2_sub(stack, &t5, &t3);
        r.x = self.fq2_sub(stack, &r.x, &t3);
        r.z = self.fq2_add(stack, &r.z, &r.y);
        r.z = self.fq2_square(stack, &r.z);
        r.z = self.fq2_sub(stack, &r.z, &t1);
        r.z = self.fq2_sub(stack, &r.z, &zsquared);
        r.y = self.fq2_sub(stack, &t3, &r.x);
        r.y = self.fq2_mul(stack, &r.y, &t4);
        let t2 = self.fq2_double(stack, &t2);
        let t2 = self.fq2_double(stack, &t2);
        let t2 = self.fq2_double(stack, &t2);
        r.y = self.fq2_sub(stack, &r.y, &t2);
        let t3 = self.fq2_mul(stack, &t4, &zsquared);
        let t3 = self.fq2_double(stack, &t3);
        let t3 = self.fq2_neg(stack, &t3);
        let t6 = self.fq2_square(stack, &t6);
        let t6 = self.fq2_sub(stack, &t6, &t0);
        let t6 = self.fq2_sub(stack, &t6, &t5);
        let t1 = self.fq2_double(stack, &t1);
        let t1 = self.fq2_double(stack, &t1);
        let t6 = self.fq2_sub(stack, &t6, &t1);
        let t0 = self.fq2_mul(stack, &r.z, &zsquared);
        let t0 = self.fq2_double(stack, &t0);
        let t0 = self.fq2_mul_by_fq(stack, &t0, g1.y());
        let t3 = self.fq2_mul_by_fq(stack, &t3, g1.x());
        *f = self.fq12_mul_by_034(stack, f, &t0, &t3, &t6);
    }

    fn add(
        &self,
        stack: &mut Stack<N>,
        f: &mut Fq12<N>,
        r: &mut Point2<N>,
        g2: &Point2Affine<N>,
        g1: &Point<Fq, N>,
    ) {
        let zsquared = self.fq2_square(stack, &r.z);
        let ysquared = self.fq2_square(stack, &g2.y);
        let t0 = self.fq2_mul(stack, &zsquared, &g2.x);
        let t1 = self.fq2_add(stack, &g2.y, &r.z);
        let t1 = self.fq2_square(stack, &t1);
        let t1 = self.fq2_sub(stack, &t1, &ysquared);
        let t1 = self.fq2_sub(stack, &t1, &zsquared);
        let t1 = self.fq2_mul(stack, &t1, &zsquared);
        let t2 = self.fq2_sub(stack, &t0, &r.x);
        let t3 = self.fq2_square(stack, &t2);
        let t4 = self.fq2_double(stack, &t3);
        let t4 = self.fq2_double(stack, &t4);
        let t5 = self.fq2_mul(stack, &t4, &t2);
        let t6 = self.fq2_sub(stack, &t1, &r.y);
        let t6 = self.fq2_sub(stack, &t6, &r.y);
        let t9 = self.fq2_mul(stack, &t6, &g2.x);
        let t7 = self.fq2_mul(stack, &t4, &r.x);
        r.x = self.fq2_square(stack, &t6);
        r.x = self.fq2_sub(stack, &r.x, &t5);
        r.x = self.fq2_sub(stack, &r.x, &t7);
        r.x = self.fq2_sub(stack, &r.x, &t7);
        r.z = self.fq2_add(stack, &r.z, &t2);
        r.z = self.fq2_square(stack, &r.z);
        r.z = self.fq2_sub(stack, &r.z, &zsquared);
        r.z = self.fq2_sub(stack, &r.z, &t3);
        let t10 = self.fq2_add(stack, &g2.y, &r.z);
        let t8 = self.fq2_sub(stack, &t7, &r.x);
        let t8 = self.fq2_mul(stack, &t8, &t6);
        let t0 = self.fq2_mul(stack, &r.y, &t5);
        let t0 = self.fq2_double(stack, &t0);
        r.y = self.fq2_sub(stack, &t8, &t0);
        let t10 = self.fq2_square(stack, &t10);
        let t10 = self.fq2_sub(stack, &t10, &ysquared);
        let ztsquared = self.fq2_square(stack, &r.z);
        let t10 = self.fq2_sub(stack, &t10, &ztsquared);
        let t9 = self.fq2_double(stack, &t9);
        let t9 = self.fq2_sub(stack, &t9, &t10);
        let t10 = self.fq2_double(stack, &r.z);
        let t6 = self.fq2_neg(stack, &t6);
        let t1 = self.fq2_double(stack, &t6);
        let t0 = self.fq2_mul_by_fq(stack, &t10, g1.y());
        let t1 = self.fq2_mul_by_fq(stack, &t1, g1.x());
        *f = self.fq12_mul_by_034(stack, f, &t0, &t1, &t9);
    }

    fn exp_by_x(&self, stack: &mut Stack<N>, f: &Fq12<N>) -> Fq12<N> {
        pub const BN_X: u64 = 4965661367192848881;
        let x = BN_X;
        let mut res = self.fq12_one(stack);
        for i in (0..63).rev() {
            // println!("i = {}", i);
            res = self.cyclotomic_square(stack, &res);
            if ((x >> i) & 1) == 1 {
                // println!("---- mul {}", i);
                res = self.fq12_mul(stack, &res, f);
            }
        }
        res
    }

    fn final_exp(&self, stack: &mut Stack<N>, f: &mut Fq12<N>) {
        let t0 = self.fq12_frobenius_map(stack, f, 6);
        let t1 = self.fq12_inverse(stack, f);
        let t1 = self.fq12_mul(stack, &t1, &t0);
        let t0 = self.fq12_frobenius_map(stack, &t1, 2);
        let t1 = self.fq12_mul(stack, &t1, &t0);
        let t0 = self.fq12_frobenius_map(stack, &t1, 1);
        let t3 = self.fq12_frobenius_map(stack, &t1, 2);
        let t4 = self.fq12_frobenius_map(stack, &t3, 1);
        let t2 = self.exp_by_x(stack, &t1);
        let t5 = self.exp_by_x(stack, &t2);
        let t6 = self.exp_by_x(stack, &t5);
        let t7 = self.fq12_frobenius_map(stack, &t2, 1);
        let t8 = self.fq12_frobenius_map(stack, &t5, 1);
        let t9 = self.fq12_frobenius_map(stack, &t6, 1);
        let t10 = self.fq12_frobenius_map(stack, &t5, 2);
        let t3 = self.fq12_mul(stack, &t3, &t0);
        let t3 = self.fq12_mul(stack, &t3, &t4);
        let t1 = self.fq12_conj(stack, &t1);
        let t4 = self.fq12_conj(stack, &t5);
        let t7 = self.fq12_conj(stack, &t7);
        let t2 = self.fq12_mul(stack, &t2, &t8);
        let t2 = self.fq12_conj(stack, &t2);
        let t9 = self.fq12_mul(stack, &t9, &t6);
        let t9 = self.fq12_conj(stack, &t9);
        let t9 = self.cyclotomic_square(stack, &t9);
        let t9 = self.fq12_mul(stack, &t9, &t2);
        let t9 = self.fq12_mul(stack, &t9, &t4);
        let t7 = self.fq12_mul(stack, &t7, &t4);
        let t7 = self.fq12_mul(stack, &t7, &t9);
        let t9 = self.fq12_mul(stack, &t9, &t10);
        let t7 = self.cyclotomic_square(stack, &t7);
        let t7 = self.fq12_mul(stack, &t7, &t9);
        let t7 = self.fq12_square(stack, &t7);
        let t1 = self.fq12_mul(stack, &t1, &t7);
        let t7 = self.fq12_mul(stack, &t7, &t3);
        let t1 = self.cyclotomic_square(stack, &t1);
        let t1 = self.fq12_mul(stack, &t1, &t7);

        *f = t1;
    }

    fn is_one(&self, stack: &mut Stack<N>, f: &Fq12<N>) -> Witness<N> {
        let mut acc = self.ch.is_one(stack, &f.c0.c0.c0);
        let next = self.ch.is_zero(stack, &f.c0.c0.c1);
        acc = stack.mul(&acc, &next);
        let next = self.ch.is_zero(stack, &f.c0.c1.c0);
        acc = stack.mul(&acc, &next);
        let next = self.ch.is_zero(stack, &f.c0.c1.c1);
        acc = stack.mul(&acc, &next);
        let next = self.ch.is_zero(stack, &f.c0.c2.c0);
        acc = stack.mul(&acc, &next);
        let next = self.ch.is_zero(stack, &f.c0.c2.c1);
        acc = stack.mul(&acc, &next);
        let next = self.ch.is_zero(stack, &f.c1.c0.c0);
        acc = stack.mul(&acc, &next);
        let next = self.ch.is_zero(stack, &f.c1.c0.c1);
        acc = stack.mul(&acc, &next);
        let next = self.ch.is_zero(stack, &f.c1.c1.c0);
        acc = stack.mul(&acc, &next);
        let next = self.ch.is_zero(stack, &f.c1.c1.c1);
        acc = stack.mul(&acc, &next);
        let next = self.ch.is_zero(stack, &f.c1.c2.c0);
        acc = stack.mul(&acc, &next);
        let next = self.ch.is_zero(stack, &f.c1.c2.c1);
        acc = stack.mul(&acc, &next);

        acc
    }

    pub fn pairing_check(
        &self,
        stack: &mut Stack<N>,
        g1: Vec<Point<Fq, N>>,
        g2: Vec<Point2Affine<N>>,
    ) -> Witness<N> {
        let mut f = self.fq12_one(stack);
        self.miller_loop(stack, &mut f, g1, g2);
        self.final_exp(stack, &mut f);
        self.is_one(stack, &f)
    }
}
