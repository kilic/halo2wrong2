use ff::PrimeField;
use halo2::{
    circuit::Layouter,
    plonk::{ConstraintSystem, Error},
};

use crate::LayoutCtx;

// pub mod crt256;
pub mod range;
pub mod rom;
pub mod select;
pub mod vanilla;
pub mod var_vanilla;
pub mod vertical;

pub trait GateLayout<F: PrimeField + Ord, E> {
    type Output;

    fn layout<L: Layouter<F>>(
        &self,
        ly_ctx: &mut LayoutCtx<F, L>,
        enforcements: E,
    ) -> Result<Self::Output, Error>;
}

pub trait GateConfig<F: PrimeField + Ord>: Clone {
    fn configure(meta: &mut ConstraintSystem<F>) -> Self;
}
