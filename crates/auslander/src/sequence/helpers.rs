use crate::hom::Morphism;
use crate::homspace::scale_morphism;
use crate::linalg::DenseMat;

/// The morphism with every entry negated.
pub(super) fn negate(f: &Morphism) -> Morphism {
    let field = f.source().field();
    scale_morphism(f, field.neg(field.one()))
}

/// The factorization `f: B -> C` with `epi.then(f) = map`, for `epi: A -> B`
/// and `map: A -> C` where `map` kills the kernel of `epi`. Every column
/// solves with free variables zeroed, so the result is deterministic; it is
/// unique when the vertex matrices of `epi` have full column rank.
///
/// One [`DenseMat::solve_many`] per vertex, not one `solve` per column: a
/// per-column solve repeats the elimination of the same `epi` matrix.
///
/// # Panics
/// Panics when a column of `map` lies outside the column space of the
/// matching `epi` matrix; callers only factor maps that kill the kernel.
pub(super) fn factor_through_epi(epi: &Morphism, map: &Morphism) -> Morphism {
    debug_assert!(epi.source().ptr_eq(map.source()));
    let field = epi.source().field();
    let nv = epi.source().algebra().quiver().num_vertices();
    let maps = (0..nv)
        .map(|v| {
            let (e, m) = (epi.map_at(v), map.map_at(v));
            // With no right-hand side there is nothing to eliminate for.
            if m.cols() == 0 {
                return DenseMat::zero(e.cols(), 0);
            }
            e.solve_many(m, &field)
                .expect("factor_through_epi: the map kills the kernel of the epimorphism")
        })
        .collect();
    Morphism::new(epi.target(), map.target(), maps)
        .expect("a factorization through an epimorphism is A-linear")
}
