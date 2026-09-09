use crate::hom::Morphism;
use crate::profile::{Site, hit};

use super::element_matrix::ElementMatrix;
use super::maps::{build_vertex_maps, injective_sum};

/// The Nakayama functor `ν = D Hom_A(−, A)` on a map between projective sums: the
/// induced morphism `⊕_k I_{sources[k]} → ⊕_l I_{targets[l]}` between the matching
/// sums of the injectives built by [`crate::module::Module::injective`].
///
/// Three steps. The `(k, l)` component of the input map is left multiplication by
/// `x = Σ_r c_r·r ∈ e_{t_l} A e_{s_k}` (see [`ElementMatrix`]). `Hom_A(−, A)`
/// turns that into right multiplication `·x: A e_{t_l} → A e_{s_k}`. `D` turns
/// that into `ν(x): D(A e_{s_k}) = I_{s_k} → D(A e_{t_l}) = I_{t_l}`. Two
/// reversals cancel, so `ν` is covariant, and `ν(P_i) = I_i` exactly.
///
/// The matrix follows from the same reading. On the dual bases of
/// [`crate::module::Module::injective`], `ν(x)(q^*) = q^* ∘ (·x)` sends a basis word
/// `p: w → t_l` to the coefficient of `q` in the normal form of `p·x`. The
/// matrix at vertex `w` has entry `Σ_r c_r · [q](p·r)` at row
/// `q ∈ paths(w, s_k)` and column `p ∈ paths(w, t_l)`.
///
/// Apply this to a minimal presentation `P_1 → P_0 → M → 0` and the kernel is the
/// AR translate. `Hom_A(−, A)` gives
/// `0 → Hom(M, A) → Hom(P_0, A) → Hom(P_1, A) → Tr M → 0`, and dualizing gives
/// `0 → τ M → ν P_1 → ν P_0 → ν M → 0`.
pub fn nu_of_presentation_map(matrix: &ElementMatrix) -> Morphism {
    hit(Site::NuOfPresentation);
    let algebra = matrix.algebra();
    let field = matrix.field();
    let positions = algebra.component_positions();
    let source = injective_sum(algebra, matrix.sources());
    let target = injective_sum(algebra, matrix.targets());
    let maps = build_vertex_maps(
        algebra,
        matrix.sources(),
        matrix.targets(),
        |s, w| algebra.paths_between(w, s).len(),
        |t, w| algebra.paths_between(w, t).len(),
        |w, k, _s, l, t, row_offset, col_offset, mat| {
            for (ri, &r) in algebra.paths_between(t, _s).iter().enumerate() {
                let c = matrix.entry(k, l)[ri];
                if c.is_zero() {
                    continue;
                }
                for (pi, &p) in algebra.paths_between(w, t).iter().enumerate() {
                    for &(q, qc) in &algebra.mul_basis(p, r) {
                        let row = row_offset + positions[q];
                        let col = col_offset + pi;
                        let add = field.mul(c, qc);
                        mat.set(row, col, field.add(mat.get(row, col), add));
                    }
                }
            }
        },
    );
    Morphism::new(&source, &target, maps)
        .expect("ν of an element matrix is A-linear between the injective sums")
}
