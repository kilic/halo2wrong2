pub mod chip;
pub mod gate;
pub mod integer;
pub mod stack;

pub mod rns;

#[cfg(test)]
mod tests;

pub(crate) fn schoolbook<'a, L: Clone, R: Clone, Out: Clone>(
    a: &'a [L],
    b: &'a [R],
) -> Vec<Vec<Out>>
where
    // L: std::ops::Mul<&'a R, Output = Out>,
    &'a L: std::ops::Mul<&'a R, Output = Out>,
{
    let mut wide = vec![vec![]; a.len() + b.len() - 1];
    for (i, a) in a.iter().enumerate() {
        for (j, b) in b.iter().enumerate() {
            wide[i + j].push(a * b);
        }
    }
    wide
}
