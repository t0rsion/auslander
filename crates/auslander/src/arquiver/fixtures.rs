use super::*;

pub(super) fn f2() -> PrimeField {
    PrimeField::new(2).unwrap()
}

pub(super) fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

pub(super) fn path_algebra(quiver: Quiver, field: PrimeField) -> Arc<Algebra> {
    crate::algebra::path_algebra(quiver, field)
        .expect("the zero ideal over an acyclic quiver completes")
}

pub(super) fn d4(field: PrimeField) -> Arc<Algebra> {
    path_algebra(
        dynkin_quiver(DynkinType::D(4)).expect("D_4 has a quiver"),
        field,
    )
}

pub(super) fn indec(m: &Module) -> IndecomposableModule {
    IndecomposableModule::new(m).expect("the fixture module is indecomposable")
}

pub(super) fn dim_vectors(quiver: &ArQuiver) -> Vec<Vec<usize>> {
    quiver
        .vertices()
        .iter()
        .map(|v| v.module().module().dim_vector().to_vec())
        .collect()
}

pub(super) fn arrow_triples(quiver: &ArQuiver) -> Vec<(usize, usize, usize)> {
    quiver
        .arrows()
        .iter()
        .map(|a| (a.source(), a.target(), a.base_dim()))
        .collect()
}

pub(super) fn flags(quiver: &ArQuiver) -> Vec<(bool, bool)> {
    quiver
        .vertices()
        .iter()
        .map(|v| (v.projective(), v.injective()))
        .collect()
}

// The F_8-endomorphism module of tests/decompose_iso.rs: the Kronecker
// representation (I_3, C) over F_2 for C the companion matrix of
// x^3 + x + 1, irreducible over F_2, so End(W) is the field F_8.
pub(super) fn f8_module() -> Module {
    let field = f2();
    let algebra = kronecker(2, field);
    let mut companion = DenseMat::zero(3, 3);
    companion.set(0, 1, field.one());
    companion.set(1, 2, field.one());
    companion.set(2, 0, field.one());
    companion.set(2, 1, field.one());
    Module::new(algebra, vec![3, 3], vec![DenseMat::identity(3), companion])
        .expect("the Kronecker representation is a module")
}
