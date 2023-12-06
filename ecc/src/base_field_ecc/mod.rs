use circuitry::{chip::Core, stack::Stack, witness::Witness};
use ff::PrimeField;
use halo2::{circuit::Value, halo2curves::CurveAffine};
use integer::{
    chip::IntegerChip,
    integer::{ConstantInteger, Integer, Range, UnassignedInteger},
    rns::Rns,
};

use crate::Point;

pub mod mul_var;
#[cfg(test)]
mod test;

#[derive(Debug, Clone)]
pub struct BaseFieldEccChip<
    C: CurveAffine,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
    const SUBLIMB_SIZE: usize,
> {
    pub ch: IntegerChip<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>,
    aux_generator: Value<C>,
    b: ConstantInteger<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
}

impl<
        C: CurveAffine,
        const NUMBER_OF_LIMBS: usize,
        const LIMB_SIZE: usize,
        const SUBLIMB_SIZE: usize,
    > BaseFieldEccChip<C, NUMBER_OF_LIMBS, LIMB_SIZE, SUBLIMB_SIZE>
{
    pub fn new(
        rns: &Rns<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
        aux_generator: Value<C>,
    ) -> Self {
        let ch = IntegerChip::new(rns);
        let b = Self::parameter_b();
        Self {
            aux_generator,
            b,
            ch,
        }
    }

    fn parameter_b() -> ConstantInteger<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
        ConstantInteger::from_fe(&C::b())
    }

    pub fn assign_scalar(
        &self,
        stack: &mut Stack<C::Scalar>,
        scalar: Value<C::Scalar>,
    ) -> Witness<C::Scalar> {
        stack.assign(scalar)
    }

    pub fn register_constant(
        &self,
        stack: &mut Stack<C::Scalar>,
        point: C,
    ) -> Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let coords = point.coordinates();
        // disallow point of infinity
        // it will not pass assing point enforcement
        let coords = coords.unwrap();
        let x = coords.x();
        let y = coords.y();
        let x = &self.ch.register_constant(stack, x);
        let y = &self.ch.register_constant(stack, y);
        Point::new(x, y)
    }

    pub fn assign_point(
        &self,
        stack: &mut Stack<C::Scalar>,
        point: Value<C>,
    ) -> Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
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
            .range(stack, &UnassignedInteger::from_fe(x), Range::Remainder);
        let y = &self
            .ch
            .range(stack, &UnassignedInteger::from_fe(y), Range::Remainder);

        let point = Point::new(x, y);
        self.assert_on_curve(stack, &point);

        point
    }

    pub fn write_rom(
        &self,
        stack: &mut Stack<C::Scalar>,
        tag: C::Scalar,
        address: C::Scalar,
        y_offset: usize,
        point: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        let y_offset = C::Scalar::from(y_offset as u64);
        // println!("x: {:?}", address);
        // println!("y: {:?}", address + y_offset);

        self.ch.write(stack, tag, address, point.x());
        self.ch.write(stack, tag, address + y_offset, point.y());
    }

    pub fn read_rom(
        &self,
        stack: &mut Stack<C::Scalar>,
        tag: C::Scalar,
        address_base: C::Scalar,
        address_fraction: &Witness<C::Scalar>,
        y_offset: usize,
    ) -> Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let y_offset = C::Scalar::from(y_offset as u64);

        let x = &self
            .ch
            .read_recover(stack, tag, address_base, address_fraction);
        let y = &self
            .ch
            .read_recover(stack, tag, address_base + y_offset, address_fraction);
        #[cfg(feature = "prover-sanity")]
        {
            let x = x.value();
            let y = y.value();
            x.zip(y)
                .map(|(x, y)| C::from_xy(x, y).expect("must be a valid point"));
        }
        Point::new(x, y)
    }

    pub fn assert_on_curve(
        &self,
        stack: &mut Stack<C::Scalar>,
        point: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        let y_square = &self.ch.square(stack, point.y(), &[]);
        let x_square = &self.ch.square(stack, point.x(), &[]);
        let x_cube = &self.ch.mul(stack, point.x(), x_square, &[]);
        let x_cube_b = &self.ch.add_constant(stack, x_cube, &self.b);
        self.ch.normal_equal(stack, x_cube_b, y_square);
    }

    pub fn copy_equal(
        &self,
        stack: &mut Stack<C::Scalar>,
        p0: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
        p1: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        self.ch.copy_equal(stack, p0.x(), p1.x());
        self.ch.copy_equal(stack, p0.y(), p1.y());
    }

    pub fn normal_equal(
        &self,
        stack: &mut Stack<C::Scalar>,
        p0: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
        p1: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) {
        // TODO: consider using normalize
        self.ch.normal_equal(stack, p0.x(), p1.x());
        self.ch.normal_equal(stack, p0.y(), p1.y());
    }

    pub fn normalize(
        &self,
        stack: &mut Stack<C::Scalar>,
        point: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let x = &self.ch.reduce(stack, point.x());
        let y = &self.ch.reduce(stack, point.y());
        Point::new(x, y)
    }

    pub fn select(
        &self,
        stack: &mut Stack<C::Scalar>,
        c: &Witness<C::Scalar>,
        p1: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
        p2: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let x = &self.ch.select(stack, p1.x(), p2.x(), c);
        let y = &self.ch.select(stack, p1.y(), p2.y(), c);
        Point::new(x, y)
    }

    pub fn select_multi(
        &self,
        stack: &mut Stack<C::Scalar>,
        selector: &[Witness<C::Scalar>],
        table: &[Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>],
    ) -> Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let number_of_selectors = selector.len();
        let mut reducer = table.to_vec();
        for (i, selector) in selector.iter().enumerate() {
            let n = 1 << (number_of_selectors - 1 - i);
            for j in 0..n {
                let k = 2 * j;
                reducer[j] = self.select(stack, selector, &reducer[k + 1], &reducer[k]);
            }
        }
        reducer[0].clone()
    }

    pub fn add_incomplete(
        &self,
        stack: &mut Stack<C::Scalar>,
        a: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
        b: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
        // lambda = b_y - a_y / b_x - a_x
        let numer = &self.ch.sub(stack, &b.y, &a.y);
        let denom = &self.ch.sub(stack, &b.x, &a.x);
        let lambda = &self.ch.div(stack, numer, denom);
        // c_x =  lambda * lambda - a_x - b_x
        let t = &self.ch.add(stack, &a.x, &b.x);
        let t = &self.ch.neg(stack, t);
        let x = &self.ch.square(stack, lambda, &[&t]);

        // c_y = lambda * (a_x - c_x) - a_y
        let t = &self.ch.sub(stack, &a.x, x);
        let y_neg = &self.ch.neg(stack, &a.y);
        let y = &self.ch.mul(stack, t, lambda, &[&y_neg]);
        Point::new(x, y)
    }

    pub fn sub_incomplete(
        &self,
        stack: &mut Stack<C::Scalar>,
        a: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
        b: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
        // lambda = b_y + a_y / a_x - b_x
        let numer = &self.ch.add(stack, &b.y, &a.y);
        let denom = &self.ch.sub(stack, &a.x, &b.x);
        let lambda = &self.ch.div(stack, numer, denom);
        // c_x =  lambda * lambda - a_x - b_x
        let t = &self.ch.add(stack, &a.x, &b.x);
        let t = &self.ch.neg(stack, t);
        let x = &self.ch.square(stack, lambda, &[&t]);

        // c_y = lambda * (a_x - c_x) - a_y
        let t = &self.ch.sub(stack, &a.x, x);
        let y_neg = &self.ch.neg(stack, &a.y);
        let y = &self.ch.mul(stack, t, lambda, &[&y_neg]);

        Point::new(x, y)
    }

    pub fn double_incomplete(
        &self,
        stack: &mut Stack<C::Scalar>,
        point: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
        // lambda = (3 * a_x^2) / 2 * a_y
        let x_0_square = &self.ch.square(stack, &point.x, &[]);
        let numer = &self.ch.mul3(stack, x_0_square);
        let denom = &self.ch.mul2(stack, &point.y);
        let lambda = &self.ch.div(stack, numer, denom);
        // c_x = lambda * lambda - 2 * a_x
        let xx = &self.ch.mul2(stack, &point.x);
        let xx_neg = &self.ch.neg(stack, xx);
        let x = &self.ch.square(stack, lambda, &[&xx_neg]);
        // c_y = lambda * (a_x - c_x) - a_y
        let t = &self.ch.sub(stack, &point.x, x);
        let y_neg = &self.ch.neg(stack, &point.y);
        let y = &self.ch.mul(stack, lambda, t, &[&y_neg]);

        // let denom = &self.ch.mul2(stack, &point.y);
        // let lambda = &self
        //     .ch
        //     .neg_mul_div(stack, &point.x.clone(), &point.x, denom);
        // let lambda = &self.ch.mul3(stack, lambda);
        // let lambda = &self.ch.neg(stack, lambda);

        // // c_x = lambda * lambda - 2 * a_x
        // let xx = &self.ch.mul2(stack, &point.x);
        // let xx_neg = &self.ch.neg(stack, xx);
        // let x = &self.ch.square(stack, lambda, &[xx_neg]);
        // // c_y = lambda * (a_x - c_x) - a_y
        // let t = &self.ch.sub(stack, &point.x, x);
        // let y_neg = &self.ch.neg(stack, &point.y);
        // let y = &self.ch.mul(stack, lambda, t, &&[&y_neg]);

        Point::new(x, y)
    }

    // ported from barretenberg
    // https://github.com/AztecProtocol/barretenberg/blob/master/cpp/src/barretenberg/stdlib/primitives/biggroup/biggroup_impl.hpp
    pub fn add_multi(
        &self,
        stack: &mut Stack<C::Scalar>,
        points: &[Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>],
    ) -> Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
        assert!(!points.is_empty());
        if points.len() == 1 {
            return points[0].clone();
        }

        struct State<
            W: PrimeField,
            N: PrimeField,
            const NUMBER_OF_LIMBS: usize,
            const LIMB_SIZE: usize,
        > {
            x_prev: Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
            y_prev: Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
            x_cur: Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
            lambda: Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        }

        let p0 = &points[0];
        let p1 = &points[1];

        let t0 = &self.ch.sub(stack, &p1.y, &p0.y);
        let t1 = &self.ch.sub(stack, &p1.x, &p0.x);
        let lambda = self.ch.div(stack, t0, t1);
        let t = &self.ch.add(stack, &p0.x, &p1.x);
        let t = &self.ch.neg(stack, t);
        let x_cur = self.ch.square(stack, &lambda, &[&t]);
        let mut state = State {
            x_prev: p0.x.clone(),
            y_prev: p0.y.clone(),
            x_cur,
            lambda,
        };

        for point in points.iter().skip(2) {
            let t = &self.ch.sub(stack, &state.x_cur, &state.x_prev);
            let denom = &self.ch.sub(stack, &state.x_cur, &point.x);
            let to_add = self.ch.add(stack, &state.y_prev, &point.y);
            let lambda = self
                .ch
                .neg_mul_div(stack, &state.lambda, t, denom, &[&to_add]);
            let t = &self.ch.add(stack, &state.x_cur, &point.x);
            let t = &self.ch.neg(stack, t);
            state.x_cur = self.ch.square(stack, &lambda, &[&t]);
            state.lambda = lambda;
            state.x_prev = point.x.clone();
            state.y_prev = point.y.clone();
        }

        let t = &self.ch.sub(stack, &state.x_prev, &state.x_cur);
        let neg_y_prev = &self.ch.neg(stack, &state.y_prev);
        let y_cur = self.ch.mul(stack, &state.lambda, t, &[&neg_y_prev]);
        Point::new(&state.x_cur, &y_cur)
    }

    // pub fn ladder_incomplete<Stack: SecondDegreeChip<C::Scalar> + FirstDegreeChip<C::Scalar>+ RangeChip<C::Scalar>>(
    //     &self,
    //     stack: &mut Stack,

    //     to_double: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
    //     to_add: &Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE>,
    // ) -> Point<C::Base, C::Scalar, NUMBER_OF_LIMBS, LIMB_SIZE> {
    //     // (P + Q) + P
    //     // P is to_double (x_1, y_1)
    //     // Q is to_add (x_2, y_2)
    //     // lambda_0 = (y_2 - y_1) / (x_2 - x_1)
    //     let numer = &self.ch.sub(stack, &to_add.y, &to_double.y);
    //     let denom = &self.ch.sub(stack, &to_add.x, &to_double.x);
    //     let lambda_0 = &self.ch.div(stack, numer, denom);
    //     // x_3 = lambda_0 * lambda_0 - x_1 - x_2
    //     let lambda_0_square = &self.ch.square(stack, lambda_0);
    //     let t = &self.ch.add(stack, &to_add.x, &to_double.x);
    //     let x_3 = &self.ch.sub(stack, lambda_0_square, t);
    //     // lambda_1 = lambda_0 + 2 * y_1 / (x_3 - x_1)
    //     let numer = &self.ch.mul2(stack, &to_double.y);
    //     let denom = &self.ch.sub(stack, x_3, &to_double.x);
    //     let lambda_1 = &self.ch.div(stack, numer, denom);
    //     let lambda_1 = &self.ch.add(stack, lambda_0, lambda_1);
    //     // x_4 = lambda_1 * lambda_1 - x_1 - x_3
    //     let lambda_1_square = &self.ch.square(stack, lambda_1);
    //     let t = &self.ch.add(stack, x_3, &to_double.x);
    //     let x_4 = &self.ch.sub(stack, lambda_1_square, t);
    //     // y_4 = lambda_1 * (x_4 - x_1) - y_1
    //     let t = &self.ch.sub(stack, x_4, &to_double.x);
    //     let t = &self.ch.mul(stack, t, lambda_1);
    //     let y_4 = &self.ch.sub(stack, t, &to_double.y);
    //     Point::new(x_4, y_4)
    // }
}
