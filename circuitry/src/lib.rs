use ff::PrimeField;
use halo2::{
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::{Advice, Any, Column, ConstraintSystem, Error, Fixed, Selector},
};
pub use halo2_pse as halo2;
use std::{collections::BTreeMap, fmt::Debug};
use witness::{Scaled, Witness};

pub type AssignedValue<F> = AssignedCell<F, F>;
pub type CellMap<F> = BTreeMap<u32, AssignedValue<F>>;

pub mod chip;
pub mod enforcement;
pub mod gates;
pub mod stack;
#[cfg(test)]
pub mod tests;
pub mod utils;
pub mod witness;

#[derive(Debug)]
pub struct LayoutCtx<F: PrimeField, L: Layouter<F>> {
    pub layouter: L,
    pub cell_map: CellMap<F>,
}

impl<F: PrimeField, L: Layouter<F>> LayoutCtx<F, L> {
    pub fn new(layouter: L) -> Self {
        LayoutCtx {
            layouter,
            cell_map: BTreeMap::new(),
        }
    }

    pub fn region<'a>(&mut self, region: Region<'a, F>) -> RegionCtx<'a, '_, F> {
        RegionCtx::new(region, &mut self.cell_map)
    }
}

#[derive(Debug)]
pub struct RegionCtx<'a, 'b, F: PrimeField> {
    region: Region<'a, F>,
    offset: usize,
    cell_map: &'b mut CellMap<F>,
}

impl<'a, 'b, F: PrimeField> RegionCtx<'a, 'b, F> {
    pub fn new(region: Region<'a, F>, cell_map: &'b mut CellMap<F>) -> RegionCtx<'a, 'b, F> {
        RegionCtx {
            region,
            offset: 0,
            cell_map,
        }
    }

    fn copy_chain(&mut self, id: u32, new: AssignedCell<F, F>) -> Result<(), Error> {
        match self.cell_map.get(&id) {
            Some(root) => self.region.constrain_equal(root.cell(), new.cell()),
            None => {
                self.cell_map.insert(id, new);
                Ok(())
            }
        }
    }

    pub fn copy(&mut self, id0: u32, id1: u32) -> Result<(), Error> {
        let cell0 = self
            .cell_map
            .get(&id0)
            .expect("must be assigned to apply copy constraint");
        let cell1 = self
            .cell_map
            .get(&id1)
            .expect("must be assigned to apply copy constraint");
        self.region.constrain_equal(cell0.cell(), cell1.cell())
    }

    pub fn offset(&self) -> usize {
        self.offset
    }

    pub fn fixed(&mut self, column: Column<Fixed>, value: F) -> Result<(), Error> {
        self.region
            .assign_fixed(|| "", column, self.offset(), || Value::known(value))?;
        Ok(())
    }

    pub fn advice(
        &mut self,
        column: Column<Advice>,
        value: Value<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        self.region
            .assign_advice(|| "", column, self.offset(), || value)
    }

    pub fn empty(&mut self, column: Column<Any>) -> Result<AssignedValue<F>, Error> {
        match column.column_type() {
            Any::Advice(_) => self.region.assign_advice(
                || "",
                column.try_into().unwrap(),
                self.offset,
                || Value::known(F::ZERO),
            ),
            Any::Fixed => self.region.assign_fixed(
                || "",
                column.try_into().unwrap(),
                self.offset,
                || Value::known(F::ZERO),
            ),
            _ => panic!("Cannot assign to instance column"),
        }
    }

    pub fn enable(&mut self, selector: Selector) -> Result<(), Error> {
        selector.enable(&mut self.region, self.offset)
    }

    pub fn next(&mut self) {
        self.offset += 1;
    }
}
