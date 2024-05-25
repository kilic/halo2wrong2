use crate::circuitry::{chip::second_degree::SecondDegreeChip, stack::Stack};
use crate::ecc::Point;
use crate::integer::{chip::IntegerChip, rns::Rns, Range};
use ff::PrimeField;
use fq12::Fq12;
use fq2::Fq2;
use halo2::halo2curves::bn256;
use halo2::{
    circuit::Value,
    halo2curves::{
        bn256::{G1Affine, G2Affine, FROBENIUS_COEFF_FQ6_C1},
        CurveAffine,
    },
};
mod fq12;
mod fq2;
mod fq6;
mod witness;

#[cfg(test)]
mod test;

pub(crate) const XI_TO_Q_MINUS_1_OVER_2: bn256::Fq2 = bn256::Fq2 {
    c0: bn256::Fq::from_raw([
        0xe4bbdd0c2936b629,
        0xbb30f162e133bacb,
        0x31a9d1b6f9645366,
        0x253570bea500f8dd,
    ]),
    c1: bn256::Fq::from_raw([
        0xa1d77ce45ffe77c7,
        0x07affd117826d1db,
        0x6d16bd27bb7edc6b,
        0x2c87200285defecc,
    ]),
};

pub(crate) const SIX_U_PLUS_2_NAF: [i8; 65] = [
    0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0,
    1, 1, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0,
    0, 1, 0, 1, 1,
];

#[derive(Clone, Debug)]
pub struct Point2<N: PrimeField> {
    x: Fq2<N>,
    y: Fq2<N>,
}

impl<N: PrimeField> Point2<N> {
    pub fn value(&self) -> Value<G2Affine> {
        self.x
            .value()
            .zip(self.y.value())
            .map(|(x, y)| G2Affine { x, y })
    }
}

#[derive(Debug, Clone)]
pub struct BNPairingChip<N: PrimeField + Ord> {
    pub ch: IntegerChip<bn256::Fq, N>,
}

impl<N: PrimeField + Ord> BNPairingChip<N> {
    pub fn new(rns: &Rns<bn256::Fq, N>, sublimb_size: usize) -> Self {
        let ch = IntegerChip::new(rns, sublimb_size);
        Self { ch }
    }

    pub fn assert_on_curve2(&self, stack: &mut Stack<N>, point: &Point2<N>) {
        let y_square = &self.fq2_square(stack, &point.y);
        let x_square = &self.fq2_square(stack, &point.x);
        let x_cube = &self.fq2_mul(stack, &point.x, x_square);
        let b = self.fq2_constant(stack, G2Affine::b());
        let x_cube_b = &self.fq2_add(stack, x_cube, &b);
        self.fq2_normal_equal(stack, x_cube_b, y_square);
    }

    pub fn assign_point2(&self, stack: &mut Stack<N>, point: Value<G2Affine>) -> Point2<N> {
        // TODO: subgroup check
        let coordinates = point.map(|point| {
            let coordinates = point.coordinates().unwrap();
            (*coordinates.x(), *coordinates.y())
        });
        let x = coordinates.map(|coordinates| coordinates.0);
        let x = self.fq2_assign(stack, x);
        let y = coordinates.map(|coordinates| coordinates.1);
        let y = self.fq2_assign(stack, y);
        let point = Point2 { x, y };
        self.assert_on_curve2(stack, &point);
        point
    }

    pub fn assert_on_curve1(&self, stack: &mut Stack<N>, point: &Point<bn256::Fq, N>) {
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
    ) -> Point<bn256::Fq, N> {
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

    pub(crate) fn prepare_g1(
        &self,
        stack: &mut Stack<N>,
        p1: &[Point<bn256::Fq, N>],
    ) -> Vec<Point<bn256::Fq, N>> {
        p1.iter()
            .map(|p1| {
                let y_prime = &self.ch.inv(stack, p1.y());
                let x_prime = &self.ch.mul(stack, p1.x(), y_prime, &[]);
                let x_prime = &self.ch.neg(stack, x_prime);
                Point::new(x_prime, y_prime)
            })
            .collect::<Vec<_>>()
    }

    pub fn pairing_check_fixed(
        &self,
        stack: &mut Stack<N>,
        p1: &[Point<bn256::Fq, N>],
        p2: &[G2Affine],
    ) {
        let (c, cube_shift) = {
            let p1: Value<Vec<G1Affine>> =
                Value::from_iter(p1.iter().map(|p1| p1.value::<G1Affine>()));
            p1.map(|p1| witness::final_exp_witness(&p1, &p2)).unzip()
        };

        let c = self.fq12_assign(stack, c);
        let c_inv = self.fq12_inverse(stack, &c);
        let mut f = c_inv.clone();
        let mut acc = p2.to_vec();

        // Prepare for simpler line equation
        let p1 = self.prepare_g1(stack, p1);

        // Run residue embedded miller loop
        for (_, x) in SIX_U_PLUS_2_NAF.iter().rev().skip(1).enumerate() {
            f = self.fq12_square(stack, &f);

            p1.iter()
                .zip(acc.iter_mut())
                .for_each(|(p1, acc)| self.double_fixed(stack, &mut f, acc, p1));

            match x {
                val @ (1 | -1) => {
                    let (negate, scale) = match val {
                        1 => (false, &c_inv),
                        -1 => (true, &c),
                        _ => unreachable!(),
                    };

                    f = self.fq12_mul(stack, &f, scale);

                    p1.iter()
                        .zip(p2.iter())
                        .zip(acc.iter_mut())
                        .for_each(|((p1, p2), acc)| {
                            self.add_fixed(stack, &mut f, acc, &p2, p1, negate);
                        });
                }
                _ => {}
            }
        }

        // Final step of miller loop
        {
            p1.iter()
                .zip(p2.iter())
                .zip(acc.iter_mut())
                .for_each(|((p1, p2), acc)| {
                    let mut p2 = p2.clone();
                    p2.x.conjugate();
                    p2.x.mul_assign(&FROBENIUS_COEFF_FQ6_C1[1]);
                    p2.y.conjugate();
                    p2.y.mul_assign(&XI_TO_Q_MINUS_1_OVER_2);
                    self.add_fixed(stack, &mut f, acc, &p2, p1, false)
                });

            p1.iter()
                .zip(p2.iter())
                .zip(acc.iter_mut())
                .for_each(|((p1, p2), acc)| {
                    let mut minusq2: G2Affine = p2.clone();
                    minusq2.x.mul_assign(&FROBENIUS_COEFF_FQ6_C1[2]);
                    self.add_fixed(stack, &mut f, acc, &minusq2, p1, false)
                });
        }

        self.residue_check(stack, c_inv, c, f, cube_shift);
    }

    pub fn pairing_check(
        &self,
        stack: &mut Stack<N>,
        p1: &[Point<bn256::Fq, N>],
        p2: &[Point2<N>],
    ) {
        let (c, cube_shift) = {
            let p1: Value<Vec<G1Affine>> =
                Value::from_iter(p1.iter().map(|p1| p1.value::<G1Affine>()));
            let p2: Value<Vec<G2Affine>> = Value::from_iter(p2.iter().map(|p2| p2.value()));

            p1.zip(p2)
                .map(|(p1, p2)| witness::final_exp_witness(&p1, &p2))
                .unzip()
        };

        let c = self.fq12_assign(stack, c);
        let c_inv = self.fq12_inverse(stack, &c);
        let mut f = c_inv.clone();
        let mut acc = p2.to_vec();

        // Prepare for simpler line equation
        let p1 = self.prepare_g1(stack, p1);

        // Run residue embedded miller loop
        for (_, x) in SIX_U_PLUS_2_NAF.iter().rev().skip(1).enumerate() {
            f = self.fq12_square(stack, &f);

            p1.iter()
                .zip(acc.iter_mut())
                .for_each(|(p1, acc)| self.double(stack, &mut f, acc, p1));

            match x {
                val @ (1 | -1) => {
                    let (negate, scale) = match val {
                        1 => (false, &c_inv),
                        -1 => (true, &c),
                        _ => unreachable!(),
                    };

                    f = self.fq12_mul(stack, &f, scale);

                    p1.iter()
                        .zip(p2.iter())
                        .zip(acc.iter_mut())
                        .for_each(|((p1, p2), acc)| {
                            self.add(stack, &mut f, acc, &p2, p1, negate);
                        });
                }
                _ => {}
            }
        }

        // Final step of miller loop
        {
            p1.iter()
                .zip(p2.iter())
                .zip(acc.iter_mut())
                .for_each(|((p1, p2), r)| {
                    let mut p2 = p2.clone();
                    p2.x = self.fq2_conj(stack, &p2.x);
                    let e = self.fq2_constant(stack, FROBENIUS_COEFF_FQ6_C1[1]);
                    p2.x = self.fq2_mul(stack, &p2.x, &e);
                    p2.y = self.fq2_conj(stack, &p2.y);
                    let e = self.fq2_constant(stack, XI_TO_Q_MINUS_1_OVER_2);
                    p2.y = self.fq2_mul(stack, &p2.y, &e);
                    self.add(stack, &mut f, r, &p2, p1, false)
                });

            p1.iter()
                .zip(p2.iter())
                .zip(acc.iter_mut())
                .for_each(|((p1, p2), acc)| {
                    let mut p2 = p2.clone();
                    let e = self.fq2_constant(stack, FROBENIUS_COEFF_FQ6_C1[2]);
                    p2.x = self.fq2_mul(stack, &p2.x, &e);
                    self.add(stack, &mut f, acc, &p2, p1, false)
                });
        }

        self.residue_check(stack, c_inv, c, f, cube_shift);
    }

    fn residue_check(
        &self,
        stack: &mut Stack<N>,
        c_inv: Fq12<N>,
        c: Fq12<N>,
        f: Fq12<N>,
        cube_shift: Value<usize>,
    ) {
        // f = f * c^(-q) * c^(2q) * c^(-3q)
        let f = {
            let u1 = self.fq12_frobenius_map(stack, &c_inv, 1);
            let u2 = self.fq12_frobenius_map(stack, &c, 2);
            let u3 = self.fq12_frobenius_map(stack, &c_inv, 3);

            let f = self.fq12_mul(stack, &f, &u1);
            let f = self.fq12_mul(stack, &f, &u2);
            self.fq12_mul(stack, &f, &u3)
        };

        // Get the correct non residue shifter
        let w0 = self.fq12_one(stack);
        let w1 = self.fq12_constant(stack, witness::w1());
        let w2 = self.fq12_constant(stack, witness::w2());

        let (b0, b1) = cube_shift
            .map(|cube_shift| match cube_shift {
                0 => (N::ZERO, N::ZERO),
                1 => (N::ONE, N::ZERO),
                2 => (N::ZERO, N::ONE),
                _ => unreachable!(),
            })
            .unzip();
        let b0 = stack.assign_bit(b0);
        let b1 = stack.assign_bit(b1);

        let s = self.fq12_select(stack, &w1, &w0, &b0);
        let s = self.fq12_select(stack, &w2, &s, &b1);

        // expect `f * c^(-q) * c^(2q) * c^(-3q) * s == 1``
        let must_be_one = self.fq12_mul(stack, &f, &s);
        let one = self.fq12_one(stack);
        let must_be_zero = self.fq12_sub(stack, &must_be_one, &one);
        self.fq12_assert_zero(stack, &must_be_zero);
    }

    fn double_fixed(
        &self,
        stack: &mut Stack<N>,
        f: &mut Fq12<N>,
        acc: &mut G2Affine,
        g1: &Point<bn256::Fq, N>,
    ) {
        let G2Affine { x: t_x, y: t_y } = *acc;
        let lambda = witness::double(acc);

        let c1 = self.fq2_mul_by_fq_constant(stack, &lambda, g1.x());
        let c3 = self.fq2_mul_by_fq_constant(stack, &(lambda * t_x - t_y), g1.y());

        self.fq12_mul_sparse(stack, f, &c1, &c3);
    }

    fn add_fixed(
        &self,
        stack: &mut Stack<N>,
        f: &mut Fq12<N>,
        acc: &mut G2Affine,
        g2: &G2Affine,
        g1: &Point<bn256::Fq, N>,
        negate: bool,
    ) {
        let G2Affine { x: t_x, y: t_y } = *acc;
        let lambda = witness::add(acc, g2, negate);

        let c1 = self.fq2_mul_by_fq_constant(stack, &lambda, g1.x());
        let c3 = self.fq2_mul_by_fq_constant(stack, &(lambda * t_x - t_y), g1.y());

        self.fq12_mul_sparse(stack, f, &c1, &c3);
    }

    fn double(
        &self,
        stack: &mut Stack<N>,
        f: &mut Fq12<N>,
        acc: &mut Point2<N>,
        g1: &Point<bn256::Fq, N>,
    ) {
        let lambda = acc.value().map(|g2| {
            let x2 = g2.x.square();
            let t0 = x2.double() + x2;
            let t1 = g2.y.double().invert().unwrap();
            let lambda = t0 * t1;
            lambda
        });
        let lambda = self.fq2_assign(stack, lambda);
        let lambda_y1 = self.fq2_mul(stack, &lambda, &acc.y);
        let two_lambda_y1 = self.fq2_double(stack, &lambda_y1);
        let x1_sq = self.fq2_square(stack, &acc.x);
        let three_x1_sq = self.fq2_mul3(stack, &x1_sq);
        self.fq2_normal_equal(stack, &two_lambda_y1, &three_x1_sq);

        let lambda_sq = self.fq2_square(stack, &lambda);
        let two_x1 = self.fq2_double(stack, &acc.x);
        let x3 = self.fq2_sub(stack, &lambda_sq, &two_x1);
        let t = self.fq2_mul(stack, &lambda, &acc.x);
        let t = self.fq2_sub(stack, &t, &acc.y);
        let t2 = self.fq2_mul(stack, &lambda, &x3);
        let y3 = self.fq2_sub(stack, &t, &t2);
        let c1 = self.fq2_mul_by_fq(stack, &lambda, g1.x());
        let c3 = self.fq2_mul_by_fq(stack, &t, g1.y());

        self.fq12_mul_sparse(stack, f, &c1, &c3);

        acc.x = self.fq2_reduce(stack, &x3);
        acc.y = self.fq2_reduce(stack, &y3);
    }

    fn add(
        &self,
        stack: &mut Stack<N>,
        f: &mut Fq12<N>,
        acc: &mut Point2<N>,
        g2: &Point2<N>,
        g1: &Point<bn256::Fq, N>,
        negate: bool,
    ) {
        let lambda = acc.value().zip(g2.value()).map(
            |(G2Affine { x: x0, y: y0 }, G2Affine { x: x1, y: y1 })| {
                let t0 = if !negate { y0 - y1 } else { y0 + y1 };
                let t1 = (x0 - x1).invert().unwrap();
                t0 * t1
            },
        );
        let lambda = self.fq2_assign(stack, lambda);
        let t0 = self.fq2_sub(stack, &acc.x, &g2.x);
        let t1 = self.fq2_mul(stack, &lambda, &t0);
        let t2 = if negate {
            self.fq2_add(stack, &acc.y, &g2.y)
        } else {
            self.fq2_sub(stack, &acc.y, &g2.y)
        };
        self.fq2_normal_equal(stack, &t1, &t2);

        let lambda_sq = self.fq2_square(stack, &lambda);
        let t = self.fq2_add(stack, &acc.x, &g2.x);
        let x3 = self.fq2_sub(stack, &lambda_sq, &t);
        let t = self.fq2_mul(stack, &lambda, &acc.x);
        let t = self.fq2_sub(stack, &t, &acc.y);
        let t2 = self.fq2_mul(stack, &lambda, &x3);
        let y3 = self.fq2_sub(stack, &t, &t2);
        let c1 = self.fq2_mul_by_fq(stack, &lambda, g1.x());
        let c3 = self.fq2_mul_by_fq(stack, &t, g1.y());

        self.fq12_mul_sparse(stack, f, &c1, &c3);

        acc.x = x3;
        acc.y = y3;
    }
}
