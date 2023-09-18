use crate::{enforcement::MemoryOperation, witness::Witness};
use ff::PrimeField;
use halo2::circuit::Value;

pub mod first_degree;
pub mod second_degree;
pub mod select;

pub trait Core<F: PrimeField> {
    // new witness with unique id
    fn new_witness(&mut self, value: Value<F>) -> Witness<F>;

    // new witness with unique id and range value
    fn new_witness_in_range(&mut self, value: Value<F>, bit_size: usize) -> Witness<F>;

    // enfoce copy equal of two witnesses
    fn equal(&mut self, w0: &Witness<F>, w1: &Witness<F>);

    // assigns new constant to a witness. if exists returns the assigned
    fn get_constant(&mut self, constant: F) -> Witness<F>;

    // constant shifters
    fn bases(&mut self, bit_size: usize) -> Vec<F>;

    // simple witness assignment
    fn assign(&mut self, value: Value<F>) -> Witness<F>;
}

pub trait Chip<Op, F: PrimeField>: Core<F> {
    fn new_op(&mut self, e: Op);
}

pub trait ROMChip<F: PrimeField + Ord, const W: usize>: Chip<MemoryOperation<F, W>, F> {
    fn write(&mut self, tag: F, address: F, values: &[Witness<F>; W]);
    fn read(&mut self, tag: F, address_base: F, address_fraction: &Witness<F>) -> [Witness<F>; W];
}
