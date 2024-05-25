use crate::{
    circuitry::stack::Stack,
    ecc::Point,
    integer::{chip::IntegerChip, rns::Rns, Range},
};
use ff::PrimeField;
use halo2::arithmetic::CurveAffine;
use halo2::{
    circuit::Value,
    halo2curves::bls12381::{self, G1Affine, G2Affine},
};

use self::{fq12::Fq12, fq2::Fq2};

mod fq12;
mod fq2;
mod fq6;
// mod witness;

#[cfg(test)]
mod test;

pub(crate) const BLS_X: [u8; 64] = [
    1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
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
pub struct BLSPairingChip<N: PrimeField + Ord> {
    pub ch: IntegerChip<bls12381::Fq, N>,
}

impl<N: PrimeField + Ord> BLSPairingChip<N> {
    pub fn new(rns: &Rns<bls12381::Fq, N>, sublimb_size: usize) -> Self {
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

    pub fn assert_on_curve1(&self, stack: &mut Stack<N>, point: &Point<bls12381::Fq, N>) {
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
    ) -> Point<bls12381::Fq, N> {
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
        p1: &[Point<bls12381::Fq, N>],
    ) -> Vec<Point<bls12381::Fq, N>> {
        p1.iter()
            .map(|p1| {
                let y_prime = &self.ch.inv(stack, p1.y());
                let x_prime = &self.ch.mul(stack, p1.x(), y_prime, &[]);
                let x_prime = &self.ch.neg(stack, x_prime);
                Point::new(x_prime, y_prime)
            })
            .collect::<Vec<_>>()
    }

    pub fn miller_loop(
        &self,
        stack: &mut Stack<N>,
        p1: &[Point<bls12381::Fq, N>],
        p2: &[Point2<N>],
    ) -> Fq12<N> {
        let mut f = self.fq12_one(stack);
        let mut acc = p2.to_vec();

        // Prepare for simpler line equation
        let p1 = self.prepare_g1(stack, p1);

        for (i, x) in BLS_X.iter().map(|&b| b == 1).skip(1).enumerate() {
            (i != 0).then(|| f = self.fq12_square(stack, &f));

            p1.iter()
                .zip(acc.iter_mut())
                .for_each(|(p1, acc)| self.double(stack, &mut f, acc, p1));

            if x {
                p1.iter()
                    .zip(p2.iter())
                    .zip(acc.iter_mut())
                    .for_each(|((p1, p2), acc)| {
                        self.add(stack, &mut f, acc, &p2, p1);
                    });
            }
        }

        self.fq12_conjugate(stack, &f)
    }

    fn double(
        &self,
        stack: &mut Stack<N>,
        f: &mut Fq12<N>,
        acc: &mut Point2<N>,
        g1: &Point<bls12381::Fq, N>,
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
        g1: &Point<bls12381::Fq, N>,
    ) {
        let lambda = acc.value().zip(g2.value()).map(
            |(G2Affine { x: x0, y: y0 }, G2Affine { x: x1, y: y1 })| {
                let t0 = y0 - y1;
                let t1 = (x0 - x1).invert().unwrap();
                t0 * t1
            },
        );
        let lambda = self.fq2_assign(stack, lambda);
        let t0 = self.fq2_sub(stack, &acc.x, &g2.x);
        let t1 = self.fq2_mul(stack, &lambda, &t0);

        let t2 = self.fq2_sub(stack, &acc.y, &g2.y);
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
