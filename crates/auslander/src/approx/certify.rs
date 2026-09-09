use super::error::ApproxError;
use crate::indec::IndecomposableModule;
use crate::iso::indecomposable_iso;
use crate::module::Module;

/// Certifies each add-generator indecomposable and the list free of repeats.
pub(super) fn certify(n_summands: &[Module]) -> Result<Vec<IndecomposableModule>, ApproxError> {
    let mut certified = Vec::with_capacity(n_summands.len());
    for (index, n) in n_summands.iter().enumerate() {
        let ind = IndecomposableModule::new(n)
            .map_err(|reason| ApproxError::SummandNotIndecomposable { index, reason })?;
        certified.push(ind);
    }
    for second in 0..certified.len() {
        for first in 0..second {
            let iso = indecomposable_iso(
                certified[first].module(),
                certified[second].module(),
                certified[first].endo(),
            );
            if iso.is_some() {
                return Err(ApproxError::RepeatedSummand { first, second });
            }
        }
    }
    Ok(certified)
}
