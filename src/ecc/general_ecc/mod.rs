use crate::circuitry::{stack::Stack, witness::Witness};
use crate::ecc::Point;
use crate::integer::{
    chip::IntegerChip,
    rns::Rns,
    {ConstantInteger, Integer, Range},
};
use ff::PrimeField;
use halo2::{circuit::Value, halo2curves::CurveAffine};

pub mod ecdsa;
pub mod mul_fix;
pub mod mul_var;

#[cfg(test)]
mod test;

#[derive(Debug, Clone)]
pub struct GeneralEccChip<Emulated: CurveAffine, N: PrimeField + Ord> {
    pub ch_base: IntegerChip<Emulated::Base, N>,
    pub ch_scalar: IntegerChip<Emulated::Scalar, N>,
    constant_aux: Emulated,
    witness_aux: Value<Emulated>,
    b: ConstantInteger<Emulated::Base, N>,
}

impl<Emulated: CurveAffine, N: PrimeField + Ord> GeneralEccChip<Emulated, N> {
    pub fn new(
        rns_base: &Rns<Emulated::Base, N>,
        rns_scalar: &Rns<Emulated::Scalar, N>,
        witness_aux: Value<Emulated>,
        constant_aux: Emulated,
        sublimb_size: usize,
    ) -> Self {
        let ch_base = IntegerChip::new(rns_base, sublimb_size);
        let ch_scalar = IntegerChip::new(rns_scalar, sublimb_size);

        let b = rns_base.constant(&Emulated::b());

        Self {
            witness_aux,
            constant_aux,
            b,
            ch_base,
            ch_scalar,
        }
    }

    pub fn assign_scalar(
        &self,
        stack: &mut Stack<N>,
        scalar: Value<Emulated::Scalar>,
    ) -> Integer<Emulated::Scalar, N> {
        let scalar = self.ch_scalar.rns().unassigned(scalar);
        self.ch_scalar
            .range(stack, &scalar, crate::integer::Range::Remainder)
    }

    pub fn register_constant(
        &self,
        stack: &mut Stack<N>,
        point: Emulated,
    ) -> Point<Emulated::Base, N> {
        let coords = point.coordinates();
        // disallow point of infinity
        // it will not pass assing point enforcement
        let coords = coords.unwrap();
        let x = coords.x();
        let y = coords.y();
        let x = &self.ch_base.register_constant(stack, x);
        let y = &self.ch_base.register_constant(stack, y);
        Point::new(x, y)
    }

    pub fn assign_point(
        &self,
        stack: &mut Stack<N>,
        point: Value<Emulated>,
    ) -> Point<Emulated::Base, N> {
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
            .ch_base
            .range(stack, &self.ch_base.rns().unassigned(x), Range::Remainder);
        let y = &self
            .ch_base
            .range(stack, &self.ch_base.rns().unassigned(y), Range::Remainder);

        let point = Point::new(x, y);
        self.assert_on_curve(stack, &point);

        point
    }

    pub fn write_rom(
        &self,
        stack: &mut Stack<N>,
        tag: N,
        address: N,
        y_offset: usize,
        point: &Point<Emulated::Base, N>,
    ) {
        let y_offset = N::from(y_offset as u64);

        self.ch_base.write(stack, tag, address, point.x());
        self.ch_base
            .write(stack, tag, address + y_offset, point.y());
    }

    pub fn read_rom(
        &self,
        stack: &mut Stack<N>,
        tag: N,
        address_base: N,
        address_fraction: &Witness<N>,
        y_offset: usize,
    ) -> Point<Emulated::Base, N> {
        let y_offset = N::from(y_offset as u64);

        let x = &self
            .ch_base
            .read_recover(stack, tag, address_base, address_fraction);
        let y = &self
            .ch_base
            .read_recover(stack, tag, address_base + y_offset, address_fraction);
        #[cfg(feature = "prover-sanity")]
        {
            let x = x.value();
            let y = y.value();
            x.zip(y)
                .map(|(x, y)| Emulated::from_xy(x, y).expect("must be a valid point"));
        }
        Point::new(x, y)
    }

    pub fn assert_on_curve(&self, stack: &mut Stack<N>, point: &Point<Emulated::Base, N>) {
        let y_square = &self.ch_base.square(stack, point.y(), &[]);
        let x_square = &self.ch_base.square(stack, point.x(), &[]);
        let x_cube = &self.ch_base.mul(stack, point.x(), x_square, &[]);
        let x_cube_b = &self.ch_base.add_constant(stack, x_cube, &self.b);
        self.ch_base.normal_equal(stack, x_cube_b, y_square);
    }

    pub fn copy_equal(
        &self,
        stack: &mut Stack<N>,
        p0: &Point<Emulated::Base, N>,
        p1: &Point<Emulated::Base, N>,
    ) {
        self.ch_base.copy_equal(stack, p0.x(), p1.x());
        self.ch_base.copy_equal(stack, p0.y(), p1.y());
    }

    pub fn normal_equal(
        &self,
        stack: &mut Stack<N>,
        p0: &Point<Emulated::Base, N>,
        p1: &Point<Emulated::Base, N>,
    ) {
        // TODO: consider using normalize
        self.ch_base.normal_equal(stack, p0.x(), p1.x());
        self.ch_base.normal_equal(stack, p0.y(), p1.y());
    }

    pub fn normalize(
        &self,
        stack: &mut Stack<N>,
        point: &Point<Emulated::Base, N>,
    ) -> Point<Emulated::Base, N> {
        let x = &self.ch_base.reduce(stack, point.x());
        let y = &self.ch_base.reduce(stack, point.y());
        Point::new(x, y)
    }

    pub fn select(
        &self,
        stack: &mut Stack<N>,
        c: &Witness<N>,
        p1: &Point<Emulated::Base, N>,
        p2: &Point<Emulated::Base, N>,
    ) -> Point<Emulated::Base, N> {
        let x = &self.ch_base.select(stack, p1.x(), p2.x(), c);
        let y = &self.ch_base.select(stack, p1.y(), p2.y(), c);
        Point::new(x, y)
    }

    pub fn select_multi(
        &self,
        stack: &mut Stack<N>,
        selector: &[Witness<N>],
        table: &[Point<Emulated::Base, N>],
    ) -> Point<Emulated::Base, N> {
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
        stack: &mut Stack<N>,
        a: &Point<Emulated::Base, N>,
        b: &Point<Emulated::Base, N>,
    ) -> Point<Emulated::Base, N> {
        // lambda = b_y - a_y / b_x - a_x
        let numer = &self.ch_base.sub(stack, &b.y, &a.y);
        let denom = &self.ch_base.sub(stack, &b.x, &a.x);
        let lambda = &self.ch_base.div(stack, numer, denom);
        // c_x =  lambda * lambda - a_x - b_x
        let t = &self.ch_base.add(stack, &a.x, &b.x);
        let t = &self.ch_base.neg(stack, t);
        let x = &self.ch_base.square(stack, lambda, &[&t]);

        // c_y = lambda * (a_x - c_x) - a_y
        let t = &self.ch_base.sub(stack, &a.x, x);
        let y_neg = &self.ch_base.neg(stack, &a.y);
        let y = &self.ch_base.mul(stack, t, lambda, &[&y_neg]);
        Point::new(x, y)
    }

    pub fn sub_incomplete(
        &self,
        stack: &mut Stack<N>,
        a: &Point<Emulated::Base, N>,
        b: &Point<Emulated::Base, N>,
    ) -> Point<Emulated::Base, N> {
        // lambda = b_y + a_y / a_x - b_x
        let numer = &self.ch_base.add(stack, &b.y, &a.y);
        let denom = &self.ch_base.sub(stack, &a.x, &b.x);
        let lambda = &self.ch_base.div(stack, numer, denom);
        // c_x =  lambda * lambda - a_x - b_x
        let t = &self.ch_base.add(stack, &a.x, &b.x);
        let t = &self.ch_base.neg(stack, t);
        let x = &self.ch_base.square(stack, lambda, &[&t]);

        // c_y = lambda * (a_x - c_x) - a_y
        let t = &self.ch_base.sub(stack, &a.x, x);
        let y_neg = &self.ch_base.neg(stack, &a.y);
        let y = &self.ch_base.mul(stack, t, lambda, &[&y_neg]);

        Point::new(x, y)
    }

    pub fn double_incomplete(
        &self,
        stack: &mut Stack<N>,
        point: &Point<Emulated::Base, N>,
    ) -> Point<Emulated::Base, N> {
        // lambda = (3 * a_x^2) / 2 * a_y
        let x_0_square = &self.ch_base.square(stack, &point.x, &[]);
        let numer = &self.ch_base.mul3(stack, x_0_square);
        let denom = &self.ch_base.mul2(stack, &point.y);
        let lambda = &self.ch_base.div(stack, numer, denom);
        // c_x = lambda * lambda - 2 * a_x
        let xx = &self.ch_base.mul2(stack, &point.x);
        let xx_neg = &self.ch_base.neg(stack, xx);
        let x = &self.ch_base.square(stack, lambda, &[&xx_neg]);
        // c_y = lambda * (a_x - c_x) - a_y
        let t = &self.ch_base.sub(stack, &point.x, x);
        let y_neg = &self.ch_base.neg(stack, &point.y);
        let y = &self.ch_base.mul(stack, lambda, t, &[&y_neg]);

        // let denom = &self.ch_base.mul2(stack, &point.y);
        // let lambda = &self
        //     .ch
        //     .neg_mul_div(stack, &point.x.clone(), &point.x, denom);
        // let lambda = &self.ch_base.mul3(stack, lambda);
        // let lambda = &self.ch_base.neg(stack, lambda);

        // // c_x = lambda * lambda - 2 * a_x
        // let xx = &self.ch_base.mul2(stack, &point.x);
        // let xx_neg = &self.ch_base.neg(stack, xx);
        // let x = &self.ch_base.square(stack, lambda, &[xx_neg]);
        // // c_y = lambda * (a_x - c_x) - a_y
        // let t = &self.ch_base.sub(stack, &point.x, x);
        // let y_neg = &self.ch_base.neg(stack, &point.y);
        // let y = &self.ch_base.mul(stack, lambda, t, &&[&y_neg]);

        Point::new(x, y)
    }

    // ported from barretenberg
    // https://github.com/AztecProtocol/barretenberg/blob/master/cpp/src/barretenberg/stdlib/primitives/biggroup/biggroup_impl.hpp
    pub fn add_multi(
        &self,
        stack: &mut Stack<N>,
        points: &[Point<Emulated::Base, N>],
    ) -> Point<Emulated::Base, N> {
        assert!(!points.is_empty());
        if points.len() == 1 {
            return points[0].clone();
        }

        struct State<W: PrimeField, N: PrimeField> {
            x_prev: Integer<W, N>,
            y_prev: Integer<W, N>,
            x_cur: Integer<W, N>,
            lambda: Integer<W, N>,
        }

        let p0 = &points[0];
        let p1 = &points[1];

        let t0 = &self.ch_base.sub(stack, &p1.y, &p0.y);
        let t1 = &self.ch_base.sub(stack, &p1.x, &p0.x);
        let lambda = self.ch_base.div(stack, t0, t1);
        let t = &self.ch_base.add(stack, &p0.x, &p1.x);
        let t = &self.ch_base.neg(stack, t);
        let x_cur = self.ch_base.square(stack, &lambda, &[&t]);
        let mut state = State {
            x_prev: p0.x.clone(),
            y_prev: p0.y.clone(),
            x_cur,
            lambda,
        };

        for point in points.iter().skip(2) {
            let t = &self.ch_base.sub(stack, &state.x_cur, &state.x_prev);
            let denom = &self.ch_base.sub(stack, &state.x_cur, &point.x);
            let to_add = self.ch_base.add(stack, &state.y_prev, &point.y);
            let lambda = self
                .ch_base
                .neg_mul_div(stack, &state.lambda, t, denom, &[&to_add]);
            let t = &self.ch_base.add(stack, &state.x_cur, &point.x);
            let t = &self.ch_base.neg(stack, t);
            state.x_cur = self.ch_base.square(stack, &lambda, &[&t]);
            state.lambda = lambda;
            state.x_prev = point.x.clone();
            state.y_prev = point.y.clone();
        }

        let t = &self.ch_base.sub(stack, &state.x_prev, &state.x_cur);
        let neg_y_prev = &self.ch_base.neg(stack, &state.y_prev);
        let y_cur = self.ch_base.mul(stack, &state.lambda, t, &[&neg_y_prev]);
        Point::new(&state.x_cur, &y_cur)
    }

    // pub fn ladder_incomplete<Stack: SecondDegreeChip<N> + FirstDegreeChip<N>+ RangeChip<N>>(
    //     &self,
    //     stack: &mut Stack,

    //     to_double: &Point<Emulated::Base, N, >,
    //     to_add: &Point<Emulated::Base, N, >,
    // ) -> Point<Emulated::Base, N, > {
    //     // (P + Q) + P
    //     // P is to_double (x_1, y_1)
    //     // Q is to_add (x_2, y_2)
    //     // lambda_0 = (y_2 - y_1) / (x_2 - x_1)
    //     let numer = &self.ch_base.sub(stack, &to_add.y, &to_double.y);
    //     let denom = &self.ch_base.sub(stack, &to_add.x, &to_double.x);
    //     let lambda_0 = &self.ch_base.div(stack, numer, denom);
    //     // x_3 = lambda_0 * lambda_0 - x_1 - x_2
    //     let lambda_0_square = &self.ch_base.square(stack, lambda_0);
    //     let t = &self.ch_base.add(stack, &to_add.x, &to_double.x);
    //     let x_3 = &self.ch_base.sub(stack, lambda_0_square, t);
    //     // lambda_1 = lambda_0 + 2 * y_1 / (x_3 - x_1)
    //     let numer = &self.ch_base.mul2(stack, &to_double.y);
    //     let denom = &self.ch_base.sub(stack, x_3, &to_double.x);
    //     let lambda_1 = &self.ch_base.div(stack, numer, denom);
    //     let lambda_1 = &self.ch_base.add(stack, lambda_0, lambda_1);
    //     // x_4 = lambda_1 * lambda_1 - x_1 - x_3
    //     let lambda_1_square = &self.ch_base.square(stack, lambda_1);
    //     let t = &self.ch_base.add(stack, x_3, &to_double.x);
    //     let x_4 = &self.ch_base.sub(stack, lambda_1_square, t);
    //     // y_4 = lambda_1 * (x_4 - x_1) - y_1
    //     let t = &self.ch_base.sub(stack, x_4, &to_double.x);
    //     let t = &self.ch_base.mul(stack, t, lambda_1);
    //     let y_4 = &self.ch_base.sub(stack, t, &to_double.y);
    //     Point::new(x_4, y_4)
    // }
}
