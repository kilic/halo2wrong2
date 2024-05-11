use std::collections::{BTreeMap, BTreeSet};

use ff::PrimeField;
use halo2::{
    circuit::{Layouter, Value},
    plonk::Error,
};

use crate::circuitry::{
    chip::{
        first_degree::FirstDegreeChip, range::RangeChip, second_degree::SecondDegreeChip,
        select::SelectChip, Chip, Core, ROMChip,
    },
    gates::{range::RangeGate, GateLayout},
    witness::{Composable, Witness},
    LayoutCtx,
};

#[derive(Clone, Debug, Default)]
pub struct Stack<F: PrimeField + Ord> {
    // to give uniques id to witnesses
    pub(crate) number_of_witnesses: u32,
    // store registred constants
    pub(crate) constants: BTreeMap<F, Witness<F>>,
    // indirect copy
    pub(crate) copy: Vec<(u32, u32)>,
    // range tables
    pub(crate) range_tables: BTreeSet<usize>,
    // ranged witnesses
    pub(crate) range_single: Vec<super::enforcement::Range<F>>,
    // ranged composition
    pub(crate) range: Vec<super::enforcement::RangeLimbs<F>>,
    // other first degree compositions
    pub(crate) first_degree: Vec<super::enforcement::FirstDegree<F>>,
    // second degree enforcements to be layouted
    pub(crate) second_degree: Vec<super::enforcement::SecondDegree<F>>,
    // selection enforcements to be layouted
    pub(crate) selections: Vec<super::enforcement::Selection<F>>,
    // ROM enforcements
    pub(crate) rom: Vec<super::enforcement::ROM<F>>,
    // memory itself
    pub(crate) rom_db: BTreeMap<F, BTreeMap<F, Vec<F>>>,
    // size of rom values
    rom_size: usize,
}

impl<F: PrimeField + Ord> Stack<F> {
    pub fn with_rom(rom_size: usize) -> Self {
        Stack::<F> {
            rom_size,
            ..Default::default()
        }
    }
}

impl<F: PrimeField + Ord> Core<F> for Stack<F> {
    fn new_witness(&mut self, value: Value<F>) -> Witness<F> {
        self.number_of_witnesses += 1;
        Witness::new(self.number_of_witnesses, value)
    }

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
}

impl<F: PrimeField + Ord> Stack<F> {
    pub fn layout_first_degree<
        L: Layouter<F>,
        Gate: GateLayout<F, Vec<super::enforcement::FirstDegree<F>>>,
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
        Gate: GateLayout<F, Vec<super::enforcement::Range<F>>>,
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
        Gate: GateLayout<F, Vec<super::enforcement::RangeLimbs<F>>>,
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
        Gate: GateLayout<F, Vec<super::enforcement::SecondDegree<F>>>,
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
        Gate: GateLayout<F, Vec<super::enforcement::Selection<F>>>,
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

    pub fn layout_rom<L: Layouter<F>, Gate: GateLayout<F, Vec<super::enforcement::ROM<F>>>>(
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
                let ctx = &mut super::RegionCtx::new(region, &mut ly.cell_map);
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

    pub fn is_one(&mut self, w0: &Witness<F>) -> Witness<F> {
        let zero = self.sub_from_constant(F::ONE, w0);
        self.is_zero(&zero)
    }

    pub fn is_equal(&mut self, w0: &Witness<F>, w1: &Witness<F>) -> Witness<F> {
        let (x, r) = w0
            .value()
            .zip(w1.value())
            .map(|(w0, w1)| {
                let dif = w0 - w1;
                Option::from(dif.invert())
                    .map(|dif_inverted| (dif_inverted, F::ZERO))
                    .unwrap_or_else(|| (F::ONE, F::ONE))
            })
            .unzip();

        let x = self.new_witness(x);
        let r = self.assign_bit(r);

        let dif = self.sub(w0, w1);

        // 0 = rx - r - x + u
        let u =
            self.compose_second_degree(&[(r * x * -F::ONE).into(), r.into(), x.into()], F::ZERO);

        // 0 = u * dif + r - 1e
        self.zero_sum_second_degree(&[(u * dif).into(), r.into()], -F::ONE);

        r
    }

    pub fn is_equal_to_constant(&mut self, w0: &Witness<F>, constant: F) -> Witness<F> {
        let (x, r) = w0
            .value()
            .map(|w0| {
                let dif = constant - w0;
                Option::from(dif.invert())
                    .map(|dif_inverted| (dif_inverted, F::ZERO))
                    .unwrap_or_else(|| (F::ONE, F::ONE))
            })
            .unzip();
        let x = self.new_witness(x);
        let r = self.assign_bit(r);
        let dif = self.sub_from_constant(constant, w0);

        // 0 = rx - r - x + u
        let u =
            self.compose_second_degree(&[(r * x * -F::ONE).into(), dif.into(), x.into()], F::ZERO);

        // 0 = u * dif + r - 1
        self.zero_sum_second_degree(&[(u * dif).into(), r.into()], -F::ONE);

        r
    }
}

impl<F: PrimeField + Ord> Chip<super::enforcement::FirstDegree<F>, F> for Stack<F> {
    fn new_op(&mut self, e: super::enforcement::FirstDegree<F>) {
        self.first_degree.push(e);
    }
}

impl<F: PrimeField + Ord> Chip<super::enforcement::RangeLimbs<F>, F> for Stack<F> {
    fn new_op(&mut self, e: super::enforcement::RangeLimbs<F>) {
        self.range.push(e);
    }
}

impl<F: PrimeField + Ord> Chip<super::enforcement::RangeOp<F>, F> for Stack<F> {
    fn new_op(&mut self, e: super::enforcement::RangeOp<F>) {
        match e {
            super::enforcement::RangeOp::Single(e) => {
                assert_ne!(e.size, 0);
                self.range_tables.insert(e.size);
                self.range_single.push(e);
            }
            super::enforcement::RangeOp::Limbs(e) => {
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

impl<F: PrimeField + Ord> Chip<super::enforcement::SecondDegree<F>, F> for Stack<F> {
    fn new_op(&mut self, e: super::enforcement::SecondDegree<F>) {
        self.second_degree.push(e);
    }
}

impl<F: PrimeField + Ord> Chip<super::enforcement::Selection<F>, F> for Stack<F> {
    fn new_op(&mut self, e: super::enforcement::Selection<F>) {
        self.selections.push(e);
    }
}

impl<F: PrimeField + Ord> SelectChip<F> for Stack<F> {}

impl<F: PrimeField + Ord> RangeChip<F> for Stack<F> {}

impl<F: PrimeField + Ord> super::chip::first_degree::FirstDegreeChip<F> for Stack<F> {}

impl<F: PrimeField + Ord> super::chip::second_degree::SecondDegreeChip<F> for Stack<F> {}

impl<F: PrimeField + Ord> Chip<super::enforcement::ROM<F>, F> for Stack<F> {
    fn new_op(&mut self, e: super::enforcement::ROM<F>) {
        self.rom.push(e);
    }
}

impl<F: PrimeField + Ord> ROMChip<F> for Stack<F> {
    fn write(&mut self, tag: F, address: F, values: &[Witness<F>]) {
        assert!(values.len() == self.rom_size);
        self.new_op(super::enforcement::ROM::Write {
            tag,
            address,
            values: values.to_vec(),
        });

        let values = values.iter().map(|value| value.value()).collect::<Vec<_>>();
        let values: Value<Vec<F>> = Value::from_iter(values);
        values.map(|values| {
            self.rom_db
                .entry(tag)
                .and_modify(|memory| {
                    assert!(memory.insert(address, values.clone()).is_none());
                })
                .or_insert_with(|| BTreeMap::from([(address, values)]));
        });
    }

    fn read(&mut self, tag: F, address_base: F, address_fraction: &Witness<F>) -> Vec<Witness<F>> {
        let values = address_fraction.value().map(|address_fraction| {
            let address = address_fraction + address_base;
            let memory = self.rom_db.get(&tag).unwrap();
            let values = memory.get(&address).unwrap();
            values.clone()
        });
        let values = values.transpose_vec(self.rom_size);
        let values = values
            .into_iter()
            .map(|value| self.new_witness(value))
            .collect::<Vec<_>>();

        self.new_op(super::enforcement::ROM::Read {
            tag,
            address_base,
            address_fraction: *address_fraction,
            values: values.clone(),
        });

        values
    }
}
