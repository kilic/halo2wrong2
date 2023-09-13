use ff::{Field, PrimeField};
use halo2::halo2curves::group::Group;
use halo2::halo2curves::CurveAffine;
#[cfg(test)]
use halo2::halo2curves::CurveExt;

macro_rules! div_ceil {
    ($a:expr, $b:expr) => {
        (($a - 1) / $b) + 1
    };
}

pub(crate) fn get_bits(segment: usize, c: usize, bytes: &[u8]) -> u64 {
    let skip_bits = segment * c;
    let skip_bytes = skip_bits / 8;

    if skip_bytes >= 32 {
        return 0;
    }

    let mut v = [0; 8];
    for (v, o) in v.iter_mut().zip(bytes[skip_bytes..].iter()) {
        *v = *o;
    }

    let mut tmp = u64::from_le_bytes(v);
    tmp >>= skip_bits - (skip_bytes * 8);
    tmp %= 1 << c;

    tmp as u64
}

pub(crate) fn binary_table<C: CurveAffine>(
    point: &C,
    aux: &C::CurveExt,
    window_size: usize,
) -> Vec<Vec<C::CurveExt>> {
    let table = incremental_table::<C>(&point.to_curve(), 1 << window_size, aux);
    let number_of_rounds = div_ceil!(C::ScalarExt::NUM_BITS as usize, window_size);
    let mut tables: Vec<Vec<C::CurveExt>> = vec![table.clone()];
    for i in 0..number_of_rounds - 1 {
        let table: Vec<C::CurveExt> = tables[i]
            .iter()
            .map(|p| (0..window_size).fold(p.clone(), |acc, _| acc.double()))
            .collect::<Vec<_>>();
        tables.push(table);
    }
    tables
}

pub(crate) fn incremental_table<C: CurveAffine>(
    point: &C::CurveExt,
    size: usize,
    aux: &C::CurveExt,
) -> Vec<C::CurveExt> {
    assert!(size > 0);
    let mut acc = aux.clone();
    (0..size)
        .map(|i| {
            let ret = acc;
            if i != size - 1 {
                acc += point;
            }
            ret
        })
        .collect()
}

fn window<F: PrimeField>(e: &F, window_size: usize) -> Vec<usize> {
    let number_of_windows = div_ceil!(F::NUM_BITS as usize, window_size);
    let e = e.to_repr();
    let mut repr: Vec<_> = (0..number_of_windows)
        .map(|i| get_bits(i, window_size, e.as_ref()) as usize)
        .collect();
    repr.reverse();
    repr
}

pub fn mul_fix<C: CurveAffine>(
    table: &[Vec<C::CurveExt>],
    scalar: &C::ScalarExt,
    window_size: usize,
) -> C::CurveExt
where
    <C::ScalarExt as PrimeField>::Repr: AsRef<[u8]>,
{
    let mut scalar = window::<_>(scalar, window_size);
    scalar.reverse();
    assert_eq!(table.len(), scalar.len());
    scalar
        .into_iter()
        .zip(table.iter())
        .fold(C::CurveExt::identity(), |acc, (coeff, table)| {
            acc + table[coeff]
        })
}

#[cfg(test)]
pub(crate) fn _mul_var_aux<C: CurveAffine>(
    point: &C,
    scalar: &C::ScalarExt,
    aux: &C,
    window_size: usize,
) -> C::CurveExt
where
    <C::ScalarExt as PrimeField>::Repr: AsRef<[u8]>,
{
    let correction = {
        let aux_table = binary_table::<C>(&C::identity(), &aux.to_curve(), window_size);
        mul_fix::<C>(&aux_table[..], &C::ScalarExt::ZERO, window_size)
    };

    let table: Vec<C::CurveExt> =
        incremental_table::<C>(&point.to_curve(), 1 << window_size, &aux.to_curve());
    let scalar = window::<_>(scalar, window_size);
    scalar
        .into_iter()
        .fold(C::CurveExt::identity(), |acc, coeff| {
            let acc = (0..window_size).fold(acc, |acc, _| acc.double());
            acc + table[coeff]
        })
        - correction
}

#[cfg(test)]
pub(crate) fn _msm_sliding_aux<C: CurveAffine>(
    points: &[C],
    scalars: &[C::ScalarExt],
    aux: &C,
    window_size: usize,
) -> C::CurveExt
where
    <C::ScalarExt as PrimeField>::Repr: AsRef<[u8]>,
{
    let number_of_points = points.len();
    assert_eq!(number_of_points, scalars.len());
    assert!(number_of_points > 0);
    let correction = {
        let mut aux = aux.to_curve();
        (0..number_of_points).fold(C::CurveExt::identity(), |acc, _| {
            let aux_table = binary_table::<C>(&C::identity(), &aux, window_size);
            aux = aux.double();
            acc + mul_fix::<C>(&aux_table[..], &C::ScalarExt::ZERO, window_size)
        })
    };
    let scalars = scalars
        .iter()
        .map(|scalar| window::<_>(scalar, window_size))
        .collect::<Vec<_>>();
    let mut aux = aux.to_curve();
    let tables = points
        .iter()
        .map(|point| {
            let table = incremental_table::<C>(&point.to_curve(), 1 << window_size, &aux);
            aux = aux.double();
            table
        })
        .collect::<Vec<Vec<C::CurveExt>>>();
    let number_of_rounds = div_ceil!(C::ScalarExt::NUM_BITS as usize, window_size);
    (0..number_of_rounds).fold(C::CurveExt::identity(), |acc, i| {
        let acc = (0..window_size).fold(acc, |acc, _| acc.double());
        tables
            .iter()
            .zip(scalars.iter())
            .fold(acc, |acc, (table, coeff)| table[coeff[i]] + acc)
    }) - correction
}

#[cfg(test)]
pub(crate) fn _multiexp_naive_var<C: CurveExt>(point: &[C], scalar: &[C::ScalarExt]) -> C
where
    <C::ScalarExt as PrimeField>::Repr: AsRef<[u8]>,
{
    assert!(!point.is_empty());
    assert_eq!(point.len(), scalar.len());
    point
        .iter()
        .zip(scalar.iter())
        .fold(C::identity(), |acc, (point, scalar)| {
            acc + (*point * *scalar)
        })
}

// pub fn mul_fix_aux<C: CurveAffine>(
//     table: &[Vec<C::CurveExt>],
//     scalar: &C::ScalarExt,
//     aux: &C,
//     window_size: usize,
// ) -> C::CurveExt
// where
//     <C::ScalarExt as PrimeField>::Repr: AsRef<[u8]>,
// {
//     let correction = {
//         let aux_table = binary_table::<C>(&C::identity(), &aux.to_curve(), window_size);
//         mul_fix::<C>(&aux_table[..], &C::ScalarExt::ZERO, window_size)
//     };

//     let mut scalar = window::<_>(scalar, window_size);
//     scalar.reverse();
//     assert_eq!(table.len(), scalar.len());
//     scalar
//         .into_iter()
//         .zip(table.iter())
//         .fold(C::CurveExt::identity(), |acc, (coeff, table)| {
//             acc + table[coeff]
//         })
//         - correction
// }
