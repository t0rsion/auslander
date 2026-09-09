use super::linear::{
    composition_rows, decomposition_holds, radical_combination_matches, row_relations,
};
use crate::context::VerificationContext;
use crate::field::Fp;
use crate::hom::Morphism;
use crate::homspace::HomSpace;
use crate::indec::IndecomposableModule;
use crate::linalg::DenseMat;
use crate::profile::{Site, hit};

/// A left `add(N)`-approximation `f: X -> B` that is left minimal, with the
/// data that proves both properties.
///
/// The only public constructor is [`crate::approx::left_approximation`], so every value
/// carries checked factorization coordinates and a checked radical
/// containment. [`MinimalLeftApproximation::verify`] recomputes all of it
/// from the stored maps.
#[derive(Debug)]
pub struct MinimalLeftApproximation {
    // f: X -> B. The endpoints are `map.source()` and `map.target()`.
    pub(super) map: Morphism,
    pub(super) summands: Vec<IndecomposableModule>,
    // B is the direct sum of `summands[slots[c]]`, in slot order.
    pub(super) slots: Vec<usize>,
    pub(super) inclusions: Vec<Morphism>,
    pub(super) projections: Vec<Morphism>,
    // factorizations[i][j]: coordinates in Hom(B, N_i) of an h with
    // f.then(h) equal to basis map j of Hom(X, N_i).
    pub(super) factorizations: Vec<Vec<Vec<Fp>>>,
    // RREF basis of K_f in End(B) coordinates.
    pub(super) kernel: DenseMat,
    // One row per kernel row: its coordinates over the RREF basis of rad End(B).
    pub(super) radical: Vec<Vec<Fp>>,
}

impl MinimalLeftApproximation {
    accessor_methods! {
        /// The approximation `f: X -> B`.
        pub map() -> &Morphism = |this| &this.map;
        /// The certified add-generators `N_1, ..., N_k`, in the given order.
        pub summands() -> &[IndecomposableModule] = |this| &this.summands;
        /// The slot list: `B` is the direct sum of `summands()[slots()[c]]`.
        pub slots() -> &[usize] = |this| &this.slots;
        /// The block inclusions `N_{slots[c]} -> B`, in slot order.
        pub inclusions() -> &[Morphism] = |this| &this.inclusions;
        /// The block projections `B -> N_{slots[c]}`, in slot order.
        pub projections() -> &[Morphism] = |this| &this.projections;
    }

    accessor_methods! {
        /// How many copies of add-generator `summand` occur in `B`.
        pub multiplicity(summand: usize) -> usize = |this| this.slots.iter().filter(|&&i| i == summand).count();
        /// Coordinates in `Hom(B, N_i)` of an `h` with `f.then(h)` equal to basis
        /// map `basis_index` of `Hom(X, N_i)`, for `i` equal to `summand`.
        ///
        /// # Panics
        /// Panics if either index is out of range.
        pub factorization(summand: usize, basis_index: usize) -> &[Fp] = |this| &this.factorizations[summand][basis_index];
        /// The RREF basis of `K_f = ker(End(B) -> Hom(X, B))` in `End(B)`
        /// coordinates, one vector per row.
        pub kernel_basis() -> &DenseMat = |this| &this.kernel;
        /// Coordinates of kernel basis row `row` over the RREF basis of
        /// `rad End(B)`.
        ///
        /// # Panics
        /// Panics if `row` is out of range.
        pub radical_coordinates(row: usize) -> &[Fp] = |this| &this.radical[row];
    }

    verify_methods!(pub(crate), { hit(Site::LeftApproximationVerify); },
        /// Recomputes every stored claim from the stored maps.
        ///
        /// The stored inclusions and projections must decompose `B` into the
        /// slot modules. `Hom(X, N_i)` and `Hom(B, N_i)` rebuild, and every
        /// stored factorization must reproduce its basis map under
        /// `f.then(h)`. `End(B)` rebuilds, and its recomputed `K_f` must equal
        /// the stored RREF basis. Each stored radical coordinate vector must
        /// reproduce its kernel row against `rad End(B)`. Nothing is replayed
        /// from the build.
        |self, context| {
        let x = self.map.source();
        let b = self.map.target();
        verify_guard!(self.factorizations.len() == self.summands.len());
        verify_guard!(self.slots.iter().all(|&i| i < self.summands.len()));
        verify_guard!(decomposition_holds(
            b,
            &self.summands,
            &self.slots,
            &self.inclusions,
            &self.projections,
        ));
        for (i, n) in self.summands.iter().enumerate() {
            let_or_false!((Ok(target_space), Ok(source_space)) =
                (HomSpace::new(x, n.module()), HomSpace::new(b, n.module())));
            verify_guard!(self.factorizations[i].len() == target_space.dim());
            for (j, coords) in self.factorizations[i].iter().enumerate() {
                verify_guard!(coords.len() == source_space.dim());
                let_or_false!(Ok(composite) = self.map.then(&source_space.morphism(coords)));
                verify_guard!(composite == target_space.basis()[j]);
            }
        }
        let endo = context.endo_for(b);
        let_or_false!(Ok(space) = HomSpace::new(x, b));
        let field = x.field();
        let_or_false!(Ok(rows) = composition_rows(&self.map, &endo, &space));
        let kernel = row_relations(&rows, space.dim(), &field);
        verify_guard!(kernel == self.kernel && self.radical.len() == kernel.rows());
        (0..kernel.rows())
            .all(|r| radical_combination_matches(&endo, &self.radical[r], kernel.row(r)))
    });
}
