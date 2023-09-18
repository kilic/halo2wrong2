use std::collections::{BTreeMap, BTreeSet};

use ff::PrimeField;
use halo2::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::{
    chip::{
        first_degree::FirstDegreeChip, second_degree::SecondDegreeChip, select::SelectChip, Chip,
        Core, ROMChip,
    },
    enforcement::{FirstDegreeComposition, MemoryOperation, SecondDegreeComposition, Selection},
    gates::{range::RangeTableLayout, GateLayout},
    witness::{Composable, Witness},
    LayoutCtx,
};

#[derive(Clone, Debug, Default)]
pub struct Stack<F: PrimeField + Ord, const MEM_W: usize> {
    // to give uniques id to witnesses
    pub(crate) number_of_witnesses: u32,
    // store registred constants
    pub(crate) constants: BTreeMap<F, Witness<F>>,
    // store arbitrary binary decomposition bases
    pub(crate) pow_of_twos: BTreeMap<usize, Vec<F>>,
    // indirect copies
    pub(crate) copies: Vec<(u32, u32)>,
    // ranged witnesses
    pub(crate) ranges: Vec<Witness<F>>,
    // final fixed tables
    pub(crate) range_tables: BTreeSet<usize>,
    // ranged composition
    pub(crate) range_compositions: Vec<FirstDegreeComposition<F>>,
    // named as ternary but can be binary as well as can include 4th operand as constant
    pub(crate) first_degree_ternary_compositions: Vec<FirstDegreeComposition<F>>,
    // other first degree compositions
    pub(crate) first_degree_compositions: Vec<FirstDegreeComposition<F>>,
    // second degree enforcements to be layouted
    pub(crate) second_degree_compositions: Vec<SecondDegreeComposition<F>>,
    // selection enforcements to be layouted
    pub(crate) selections: Vec<Selection<F>>,
    // ROM enforcements
    pub(crate) rom: Vec<MemoryOperation<F, MEM_W>>,
    // memory itself
    pub(crate) memory: BTreeMap<F, BTreeMap<F, [F; MEM_W]>>,
}

// Essentias
impl<F: PrimeField + Ord, const MEM_W: usize> Core<F> for Stack<F, MEM_W> {
    fn new_witness(&mut self, value: Value<F>) -> Witness<F> {
        self.number_of_witnesses += 1;
        Witness::new(self.number_of_witnesses, value)
    }

    fn new_witness_in_range(&mut self, value: Value<F>, bit_size: usize) -> Witness<F> {
        self.number_of_witnesses += 1;
        let witness = Witness::new_in_range(self.number_of_witnesses, value, bit_size);
        self.ranges.push(witness);
        self.range_tables.insert(bit_size);
        witness
    }

    fn equal(&mut self, w0: &Witness<F>, w1: &Witness<F>) {
        match (w0.id, w1.id) {
            (Some(id0), Some(id1)) => {
                self.copies.push((id0, id1));
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

    fn bases(&mut self, bit_size: usize) -> Vec<F> {
        macro_rules! div_ceil {
            ($a:expr, $b:expr) => {
                (($a - 1) / $b) + 1
            };
        }
        self.pow_of_twos
            .entry(bit_size)
            .or_insert_with(|| {
                (0..div_ceil!(F::NUM_BITS as usize, bit_size))
                    .map(|i| F::from(2).pow([(bit_size * i) as u64, 0, 0, 0]))
                    .collect()
            })
            .clone()
    }
}

impl<F: PrimeField + Ord, const MEM_W: usize> Stack<F, MEM_W> {
    pub fn layout_first_degree_compositions<
        L: Layouter<F>,
        Gate: GateLayout<F, Vec<FirstDegreeComposition<F>>>,
    >(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
        gate: &Gate,
    ) -> Result<(), Error> {
        println!("Layout first degree compositions");
        let e = std::mem::take(&mut self.first_degree_compositions);
        gate.layout(ly, e)?;
        Ok(())
    }

    pub fn layout_range_compositions<
        L: Layouter<F>,
        Gate: GateLayout<F, Vec<FirstDegreeComposition<F>>>,
    >(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
        gate: &Gate,
    ) -> Result<(), Error> {
        println!("Layout range compositions");
        let e = std::mem::take(&mut self.range_compositions);
        gate.layout(ly, e)?;
        Ok(())
    }

    pub fn layout_first_degree_ternary_compositions<
        L: Layouter<F>,
        Gate: GateLayout<F, Vec<FirstDegreeComposition<F>>>,
    >(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
        gate: &Gate,
    ) -> Result<(), Error> {
        println!("Layout simple composition (ternaries with a constant)");
        let e = std::mem::take(&mut self.first_degree_ternary_compositions);
        gate.layout(ly, e)?;
        Ok(())
    }

    #[cfg(test)]
    pub fn layout_first_degree_ternary_compositions_no_constant<
        L: Layouter<F>,
        Gate: GateLayout<F, Vec<FirstDegreeComposition<F>>>,
    >(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
        gate: &Gate,
    ) -> Result<(), Error> {
        println!("Layout simple composition no constant");
        let e = std::mem::take(&mut self.first_degree_ternary_compositions);
        let e: Vec<_> = e.iter().filter(|e| !e.has_constant()).cloned().collect();
        gate.layout(ly, e)?;
        Ok(())
    }

    pub fn layout_second_degree_compositions<
        L: Layouter<F>,
        Gate: GateLayout<F, Vec<SecondDegreeComposition<F>>>,
    >(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
        gate: &Gate,
    ) -> Result<(), Error> {
        println!("Layout second degree composition");
        let e = std::mem::take(&mut self.second_degree_compositions);
        gate.layout(ly, e)?;
        Ok(())
    }

    pub fn layout_selections<L: Layouter<F>, Gate: GateLayout<F, Vec<Selection<F>>>>(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
        gate: &Gate,
    ) -> Result<(), Error> {
        println!("Layout selections");
        let e = std::mem::take(&mut self.selections);
        gate.layout(ly, e)?;
        Ok(())
    }

    pub fn layout_rom<L: Layouter<F>, Gate: GateLayout<F, Vec<MemoryOperation<F, MEM_W>>>>(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
        gate: &Gate,
    ) -> Result<(), Error> {
        println!("Layout ROM");
        let e = std::mem::take(&mut self.rom);
        gate.layout(ly, e)?;
        Ok(())
    }

    pub fn layout_range_tables<L: Layouter<F>, Gate: RangeTableLayout<F>>(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
        gate: &Gate,
    ) -> Result<(), Error> {
        println!("Layout range tables");
        let mut tables: Vec<_> = self.range_tables.iter().copied().collect();
        tables.sort();
        #[cfg(feature = "synth-sanity")]
        {
            assert_eq!(range_sizes(&self.ranges[..]), tables);
        }
        gate.layout_range_tables(ly, &tables)
    }

    pub fn apply_indirect_copies<L: Layouter<F>>(
        &mut self,
        ly: &mut LayoutCtx<F, L>,
    ) -> Result<(), Error> {
        ly.layouter.assign_region(
            || "",
            |region| {
                let ctx = &mut crate::RegionCtx::new(region, &mut ly.cell_map);

                for (id0, id1) in self.copies.iter() {
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

impl<F: PrimeField + Ord, const MEM_W: usize> Chip<FirstDegreeComposition<F>, F>
    for Stack<F, MEM_W>
{
    fn new_op(&mut self, e: FirstDegreeComposition<F>) {
        if e.is_range_demoposition() {
            self.range_compositions.push(e)
        } else {
            if e.is_simple() {
                self.first_degree_ternary_compositions.push(e);
            } else {
                self.first_degree_compositions.push(e);
            }
        }
    }
}

impl<F: PrimeField + Ord, const MEM_W: usize> Chip<SecondDegreeComposition<F>, F>
    for Stack<F, MEM_W>
{
    fn new_op(&mut self, e: SecondDegreeComposition<F>) {
        self.second_degree_compositions.push(e);
    }
}

impl<F: PrimeField + Ord, const MEM_W: usize> Chip<Selection<F>, F> for Stack<F, MEM_W> {
    fn new_op(&mut self, e: Selection<F>) {
        self.selections.push(e);
    }
}

impl<F: PrimeField + Ord, const MEM_W: usize> SelectChip<F> for Stack<F, MEM_W> {}

impl<F: PrimeField + Ord, const MEM_W: usize> crate::chip::first_degree::FirstDegreeChip<F>
    for Stack<F, MEM_W>
{
}

impl<F: PrimeField + Ord, const MEM_W: usize> crate::chip::second_degree::SecondDegreeChip<F>
    for Stack<F, MEM_W>
{
}

impl<F: PrimeField + Ord, const MEM_W: usize> Chip<MemoryOperation<F, MEM_W>, F>
    for Stack<F, MEM_W>
{
    fn new_op(&mut self, e: MemoryOperation<F, MEM_W>) {
        self.rom.push(e);
    }
}

impl<F: PrimeField + Ord, const W: usize> ROMChip<F, W> for Stack<F, W> {
    fn write(&mut self, tag: F, address: F, values: &[Witness<F>; W]) {
        self.new_op(MemoryOperation::Write {
            tag,
            address,
            values: values.clone(),
        });

        let values = values.iter().map(|value| value.value()).collect::<Vec<_>>();
        let values: Value<Vec<F>> = Value::from_iter(values);
        values.map(|values| {
            let values = values.try_into().unwrap();
            self.memory
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
            let memory = self.memory.get(&tag).unwrap();
            let values = memory.get(&address).unwrap();
            values.clone()
        });
        let values = values.transpose_array();
        let values = values
            .into_iter()
            .map(|value| self.new_witness(value))
            .collect::<Vec<_>>();
        let values = values.try_into().unwrap();

        self.new_op(MemoryOperation::Read {
            tag,
            address_base,
            address_fraction: address_fraction.clone(),
            values,
        });

        values
    }
}
