use std::collections::{BTreeMap, BTreeSet};

use ff::PrimeField;
use halo2::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::{
    chip::{
        first_degree::FirstDegreeChip, range::RangeChip, second_degree::SecondDegreeChip,
        select::SelectChip, Chip, Core, ROMChip,
    },
    gates::{range::RangeGate, GateLayout},
    witness::{Composable, Witness},
    LayoutCtx,
};

#[derive(Clone, Debug, Default)]
pub struct Stack<F: PrimeField + Ord, const ROM_W: usize> {
    // to give uniques id to witnesses
    pub(crate) number_of_witnesses: u32,
    // store registred constants
    pub(crate) constants: BTreeMap<F, Witness<F>>,
    // indirect copy
    pub(crate) copy: Vec<(u32, u32)>,
    // range tables
    pub(crate) range_tables: BTreeSet<usize>,
    // ranged witnesses
    pub(crate) range_single: Vec<crate::enforcement::Range<F>>,
    // ranged composition
    pub(crate) range: Vec<crate::enforcement::RangeLimbs<F>>,
    // other first degree compositions
    pub(crate) first_degree: Vec<crate::enforcement::FirstDegree<F>>,
    // second degree enforcements to be layouted
    pub(crate) second_degree: Vec<crate::enforcement::SecondDegree<F>>,
    // selection enforcements to be layouted
    pub(crate) selections: Vec<crate::enforcement::Selection<F>>,
    // ROM enforcements
    pub(crate) rom: Vec<crate::enforcement::ROM<F, ROM_W>>,
    // memory itself
    pub(crate) rom_db: BTreeMap<F, BTreeMap<F, [F; ROM_W]>>,
}

impl<F: PrimeField + Ord, const ROM_W: usize> Core<F> for Stack<F, ROM_W> {
    fn new_witness(&mut self, value: Value<F>) -> Witness<F> {
        self.number_of_witnesses += 1;
        Witness::new(self.number_of_witnesses, value)
    }

    // fn new_witness_in_range(&mut self, value: Value<F>, bit_size: usize) -> Witness<F> {
    //     self.number_of_witnesses += 1;
    //     let witness = Witness::new_in_range(self.number_of_witnesses, value, bit_size);
    //     self.range_tables.insert(bit_size);
    //     witness
    // }

    fn equal(&mut self, w0: &Witness<F>, w1: &Witness<F>) {
        match (w0.id, w1.id) {
            (Some(id0), Some(id1)) => {
                self.copy.push((id0, id1));
            }
            _ => panic!("cannot copy tmp witness"),
        }
    }

    fn get_constant(&mut self, constant: F) -> Witness<F> {
        match self.constants.get(&constant) {
            Some(constant) => *constant,
            _ => {
                let w = self.new_witness(Value::known(constant));
                self.equal_to_constant(&w, constant);
                assert!(self.constants.insert(constant, w).is_none());
                w
            }
        }
    }

    fn assign(&mut self, value: Value<F>) -> Witness<F> {
        let w = self.new_witness(value);
        // TODO: this is tmp workarounde
        // related with exploiting Scaled::dummy
        self.zero_sum(&[w.add(), w.sub()], F::ZERO);
        w
    }

    // fn bases(&mut self, bit_size: usize) -> Vec<F> {
    //     macro_rules! div_ceil {
    //         ($a:expr, $b:expr) => {
    //             (($a - 1) / $b) + 1
    //         };
    //     }
    //     self.pow_of_twos
    //         .entry(bit_size)
    //         .or_insert_with(|| {
    //             (0..div_ceil!(F::NUM_BITS as usize, bit_size))
    //                 .map(|i| F::from(2).pow([(bit_size * i) as u64, 0, 0, 0]))
    //                 .collect()
    //         })
    //         .clone()
    // }
}

impl<F: PrimeField + Ord, const ROM_W: usize> Stack<F, ROM_W> {
    pub fn layout_first_degree<
        L: Layouter<F>,
        Gate: GateLayout<F, Vec<crate::enforcement::FirstDegree<F>>>,
    >(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
        gate: &Gate,
    ) -> Result<(), Error> {
        println!("Layout first degree compositions");
        let e = std::mem::take(&mut self.first_degree);
        gate.layout(ly, e)?;
        Ok(())
    }

    pub fn layout_range_single<
        L: Layouter<F>,
        Gate: GateLayout<F, Vec<crate::enforcement::Range<F>>>,
    >(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
        gate: &Gate,
    ) -> Result<(), Error> {
        println!("Layout single cell ranges");
        let e = std::mem::take(&mut self.range_single);
        gate.layout(ly, e)?;
        Ok(())
    }

    pub fn layout_range_limbs<
        L: Layouter<F>,
        Gate: GateLayout<F, Vec<crate::enforcement::RangeLimbs<F>>>,
    >(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
        gate: &Gate,
    ) -> Result<(), Error> {
        println!("Layout range compositions");
        let e = std::mem::take(&mut self.range);
        gate.layout(ly, e)?;
        Ok(())
    }

    pub fn layout_second_degree<
        L: Layouter<F>,
        Gate: GateLayout<F, Vec<crate::enforcement::SecondDegree<F>>>,
    >(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
        gate: &Gate,
    ) -> Result<(), Error> {
        println!("Layout second degree composition");
        let e = std::mem::take(&mut self.second_degree);
        gate.layout(ly, e)?;
        Ok(())
    }

    pub fn layout_selections<
        L: Layouter<F>,
        Gate: GateLayout<F, Vec<crate::enforcement::Selection<F>>>,
    >(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
        gate: &Gate,
    ) -> Result<(), Error> {
        println!("Layout selections");
        let e = std::mem::take(&mut self.selections);
        gate.layout(ly, e)?;
        Ok(())
    }

    pub fn layout_rom<
        L: Layouter<F>,
        Gate: GateLayout<F, Vec<crate::enforcement::ROM<F, ROM_W>>>,
    >(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
        gate: &Gate,
    ) -> Result<(), Error> {
        println!("Layout ROM");
        let e = std::mem::take(&mut self.rom);
        gate.layout(ly, e)?;
        Ok(())
    }

    pub fn layout_range_tables<L: Layouter<F>>(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
        gate: &RangeGate,
    ) -> Result<(), Error> {
        println!("Layout range tables");
        let mut tables: Vec<_> = self.range_tables.iter().copied().collect();
        tables.sort();
        gate.layout_range_tables(ly, &tables)
    }

    pub fn apply_indirect_copy<L: Layouter<F>>(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
    ) -> Result<(), Error> {
        ly.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut crate::RegionCtx::new(region, &mut ly.cell_map);
                for (id0, id1) in self.copy.iter() {
                    ctx.copy(*id0, *id1)?;
                }
                Ok(())
            },
        )
    }

    pub fn assert_not_equal(&mut self, w0: &Witness<F>, w1: &Witness<F>) {
        let u = self.sub(w0, w1);
        self.assert_not_zero(&u)
    }
}

impl<F: PrimeField + Ord, const ROM_W: usize> Chip<crate::enforcement::FirstDegree<F>, F>
    for Stack<F, ROM_W>
{
    fn new_op(&mut self, e: crate::enforcement::FirstDegree<F>) {
        self.first_degree.push(e);
    }
}

impl<F: PrimeField + Ord, const ROM_W: usize> Chip<crate::enforcement::RangeLimbs<F>, F>
    for Stack<F, ROM_W>
{
    fn new_op(&mut self, e: crate::enforcement::RangeLimbs<F>) {
        self.range.push(e);
    }
}

impl<F: PrimeField + Ord, const ROM_W: usize> Chip<crate::enforcement::RangeOp<F>, F>
    for Stack<F, ROM_W>
{
    fn new_op(&mut self, e: crate::enforcement::RangeOp<F>) {
        match e {
            crate::enforcement::RangeOp::Single(e) => {
                assert_ne!(e.size, 0);
                self.range_tables.insert(e.size);
                self.range_single.push(e);
            }
            crate::enforcement::RangeOp::Limbs(e) => {
                assert_ne!(e.limb_size, 0);

                self.range_tables.insert(e.limb_size);
                if let Some(size) = e.overflow_size {
                    assert_ne!(e.limb_size, size);
                    self.range_tables.insert(size);
                }

                self.range.push(e);
            }
        }
    }
}

impl<F: PrimeField + Ord, const ROM_W: usize> Chip<crate::enforcement::SecondDegree<F>, F>
    for Stack<F, ROM_W>
{
    fn new_op(&mut self, e: crate::enforcement::SecondDegree<F>) {
        self.second_degree.push(e);
    }
}

impl<F: PrimeField + Ord, const ROM_W: usize> Chip<crate::enforcement::Selection<F>, F>
    for Stack<F, ROM_W>
{
    fn new_op(&mut self, e: crate::enforcement::Selection<F>) {
        self.selections.push(e);
    }
}

impl<F: PrimeField + Ord, const ROM_W: usize> SelectChip<F> for Stack<F, ROM_W> {}

impl<F: PrimeField + Ord, const ROM_W: usize> RangeChip<F> for Stack<F, ROM_W> {}

impl<F: PrimeField + Ord, const ROM_W: usize> crate::chip::first_degree::FirstDegreeChip<F>
    for Stack<F, ROM_W>
{
}

impl<F: PrimeField + Ord, const ROM_W: usize> crate::chip::second_degree::SecondDegreeChip<F>
    for Stack<F, ROM_W>
{
}

impl<F: PrimeField + Ord, const ROM_W: usize> Chip<crate::enforcement::ROM<F, ROM_W>, F>
    for Stack<F, ROM_W>
{
    fn new_op(&mut self, e: crate::enforcement::ROM<F, ROM_W>) {
        self.rom.push(e);
    }
}

impl<F: PrimeField + Ord, const W: usize> ROMChip<F, W> for Stack<F, W> {
    fn write(&mut self, tag: F, address: F, values: &[Witness<F>; W]) {
        self.new_op(crate::enforcement::ROM::Write {
            tag,
            address,
            values: *values,
        });

        let values = values.iter().map(|value| value.value()).collect::<Vec<_>>();
        let values: Value<Vec<F>> = Value::from_iter(values);
        values.map(|values| {
            let values = values.try_into().unwrap();
            self.rom_db
                .entry(tag)
                .and_modify(|memory| {
                    assert!(memory.insert(address, values).is_none());
                })
                .or_insert_with(|| BTreeMap::from([(address, values)]));
        });
    }

    fn read(&mut self, tag: F, address_base: F, address_fraction: &Witness<F>) -> [Witness<F>; W] {
        let values = address_fraction.value().map(|address_fraction| {
            let address = address_fraction + address_base;
            let memory = self.rom_db.get(&tag).unwrap();
            let values = memory.get(&address).unwrap();
            *values
        });
        let values = values.transpose_array();
        let values = values
            .into_iter()
            .map(|value| self.new_witness(value))
            .collect::<Vec<_>>();
        let values = values.try_into().unwrap();

        self.new_op(crate::enforcement::ROM::Read {
            tag,
            address_base,
            address_fraction: *address_fraction,
            values,
        });

        values
    }
}
