use circuitry::witness::Witness;
use ff::PrimeField;
use halo2::{circuit::Value, halo2curves::CurveAffine};
use integer::integer::{ConstantInteger, Integer};

pub mod base_field_ecc;
pub mod general_ecc;

#[derive(Clone, Debug)]
pub struct Point<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>
{
    x: Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    y: Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
}

impl<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>
    Point<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>
{
    pub fn new(
        x: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
        y: &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    ) -> Point<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        Point {
            x: x.clone(),
            y: y.clone(),
        }
    }

    pub fn public(&self) -> Vec<Witness<N>> {
        self.x
            .limbs()
            .iter()
            .chain(self.y.limbs().iter())
            .cloned()
            .collect()
    }

    pub fn x(&self) -> &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        &self.x
    }

    pub fn y(&self) -> &Integer<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        &self.y
    }

    pub fn value<C>(&self) -> Value<C>
    where
        // C: CurveAffine<Base = W, ScalarExt = N>,
        C: CurveAffine<Base = W>,
    {
        let x = self.x.value();
        let y = self.y.value();
        x.zip(y).map(|(x, y)| C::from_xy(x, y).unwrap())
    }
}

#[derive(Clone, Debug)]
pub struct ConstantPoint<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const LIMB_SIZE: usize,
> {
    x: ConstantInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
    y: ConstantInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>,
}
impl<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const LIMB_SIZE: usize>
    ConstantPoint<W, N, NUMBER_OF_LIMBS, LIMB_SIZE>
{
    pub fn new<Emulated: CurveAffine>(
        point: Emulated,
    ) -> ConstantPoint<Emulated::Base, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        let coords = point.coordinates();
        // disallow point of infinity
        // it will not pass assing point enforcement
        let coords = coords.unwrap();
        let x = coords.x();
        let y = coords.y();
        ConstantPoint {
            x: ConstantInteger::from_fe(x),
            y: ConstantInteger::from_fe(y),
        }
    }

    pub fn x(&self) -> &ConstantInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        &self.x
    }

    pub fn y(&self) -> &ConstantInteger<W, N, NUMBER_OF_LIMBS, LIMB_SIZE> {
        &self.y
    }

    pub fn value<C>(&self) -> C
    where
        C: CurveAffine<Base = W, ScalarExt = N>,
    {
        let x = self.x.value();
        let y = self.y.value();
        C::from_xy(x, y).unwrap()
    }
}

#[cfg(test)]
mod test {

    use ark_std::{end_timer, start_timer};
    use halo2::halo2curves::bn256::{Bn256, Fr};
    use halo2::plonk::Circuit;
    use halo2::plonk::{create_proof, keygen_pk, keygen_vk};
    use halo2::poly::commitment::ParamsProver;
    use halo2::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
    use halo2::poly::kzg::multiopen::ProverSHPLONK;
    use halo2::transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer};
    use rand_core::OsRng;

    pub(crate) fn write_srs(k: u32) -> ParamsKZG<Bn256> {
        let path = format!("srs_{k}.bin");
        let params = ParamsKZG::<Bn256>::new(k);
        params
            .write_custom(
                &mut std::fs::File::create(path).unwrap(),
                halo2::SerdeFormat::RawBytesUnchecked,
            )
            .unwrap();
        params
    }

    pub(crate) fn read_srs(k: u32) -> ParamsKZG<Bn256> {
        let path = format!("srs_{k}.bin");
        let file = std::fs::File::open(path.as_str());
        match file {
            Ok(mut file) => {
                ParamsKZG::<Bn256>::read_custom(&mut file, halo2::SerdeFormat::RawBytesUnchecked)
                    .unwrap()
            }
            Err(_) => write_srs(k),
        }
    }

    pub(crate) fn run_test_prover(k: u32, circuit: impl Circuit<Fr>) {
        println!("params read");
        let params = read_srs(k);
        println!("gen vk");
        let vk = keygen_vk(&params, &circuit).unwrap();
        println!("gen pk");
        let pk = keygen_pk(&params, vk, &circuit).unwrap();
        println!("pk write");

        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

        let t0 = start_timer!(|| "prover");
        let proof = create_proof::<KZGCommitmentScheme<Bn256>, ProverSHPLONK<Bn256>, _, _, _, _>(
            &params,
            &pk,
            &[circuit],
            &[&[]],
            OsRng,
            &mut transcript,
        );
        end_timer!(t0);

        proof.expect("proof generation should not fail");
    }
}
