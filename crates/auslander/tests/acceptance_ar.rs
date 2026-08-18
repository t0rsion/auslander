//! v0.4 acceptance matrix for the AR layer (design sections 12, 13, 18).
//!
//! Tier 1 runs on the full non-monomial matrix plus monomial fixtures: the
//! commutative square kQ/(ab - cd) over F_5, the preprojective algebra of
//! A_3 over F_2, the inhomogeneous algebra kQ/(ab - cde) over F_5,
//! k[x]/(x^3) over F_2 and F_5, and linearly oriented A_3 over F_5. It
//! covers Ext space dimensions, the Yoneda product laws on every bounded
//! basis tuple, extensions built from degree 1 classes, AR-duality
//! almost-split sequences, and stable Hom.
//!
//! Tier 2 runs only where an exhaustive catalog exists: k[x]/(x^3) over
//! F_2 and F_5, linear A_3 over F_5, the radical-square-zero 3-cycle over
//! F_5, and the zero-ideal D_4 path algebra over F_2. It covers the AR
//! quiver, the middle-term cross-check gate of design section 12, the
//! catalog witness route, and arrow valuations. The preprojective algebra
//! of A_3 is representation finite but carries no certified catalog in
//! this release, so it runs tier 1 only and the AR quiver dispatch rejects
//! it with both carried reasons.

use std::collections::HashMap;
use std::sync::{Arc, OnceLock};

use auslander::algebra::{
    Algebra, commutative_square, linear_an, path_algebra, radical_square_zero_cycle, truncated_poly,
};
use auslander::almost_split::{AlmostSplitOutcome, almost_split, stable_end, stable_hom};
use auslander::ar::tau;
use auslander::arquiver::{ArQuiver, ArQuiverError, ArrowValuation, ar_quiver};
use auslander::decompose::{KrullSchmidtOutcome, krull_schmidt};
use auslander::dynkin::{DynkinError, DynkinType, dynkin_quiver};
use auslander::enumerate::EnumerateError;
use auslander::ext::{ExtClass, ExtClassError, ExtSpace, ext_dim};
use auslander::field::{Fp, PrimeField};
use auslander::hom::{Morphism, hom_dim};
use auslander::homspace::HomSpace;
use auslander::indec::IndecomposableModule;
use auslander::linalg::DenseMat;
use auslander::module::Module;
use auslander::quiver::ArrowId;
use auslander::radical::radical;
use auslander::sequence::{ShortExactSequence, SplitStatus};

/// Products run on every basis tuple whose degrees sum to at most this.
const MAX_DEGREE: usize = 3;

mod common;

use common::{
    basis_class, catalog_sequence, catalog_witness, duality_sequence, duality_witness, f2, f5,
    inhomogeneous, preprojective_a3,
};

fn tier1_fixtures() -> Vec<(&'static str, Arc<Algebra>)> {
    vec![
        ("commutative-square-f5", commutative_square(f5())),
        ("preprojective-a3-f2", preprojective_a3()),
        ("inhomogeneous-f5", inhomogeneous()),
        ("truncated-poly-3-f2", truncated_poly(3, f2()).unwrap()),
        ("truncated-poly-3-f5", truncated_poly(3, f5()).unwrap()),
        ("linear-a3-f5", linear_an(3, f5())),
    ]
}

/// The zero-ideal path algebra of the D_4 quiver oriented away from the
/// branch vertex 0: arrows 0 -> 1, 0 -> 2, 0 -> 3.
fn d4_zero_ideal(field: PrimeField) -> Arc<Algebra> {
    let quiver = dynkin_quiver(DynkinType::D(4)).expect("D_4 has a quiver");
    path_algebra(quiver, field).expect("the zero ideal over an acyclic quiver completes")
}

fn tier2_domains() -> Vec<(&'static str, Arc<Algebra>)> {
    vec![
        ("truncated-poly-3-f2", truncated_poly(3, f2()).unwrap()),
        ("truncated-poly-3-f5", truncated_poly(3, f5()).unwrap()),
        ("linear-a3-f5", linear_an(3, f5())),
        (
            "radical-square-zero-cycle-3-f5",
            radical_square_zero_cycle(3, f5()),
        ),
        ("d4-f2", d4_zero_ideal(f2())),
    ]
}

/// The simples of one algebra with their Ext dimensions up to
/// [`MAX_DEGREE`] and every nonzero space, built once per fixture. The
/// simples are shared `Module` values, so every space in the map is
/// pointer-compatible with every other space on the same endpoints.
struct SimpleExt {
    simples: Vec<Module>,
    dims: Vec<Vec<Vec<usize>>>,
    spaces: HashMap<(usize, usize, usize), ExtSpace>,
}

impl SimpleExt {
    fn new(algebra: &Arc<Algebra>) -> SimpleExt {
        let n = algebra.quiver().num_vertices();
        let simples: Vec<Module> = (0..n).map(|v| Module::simple(algebra, v)).collect();
        let count = simples.len();
        let mut dims = vec![vec![vec![0usize; MAX_DEGREE + 1]; count]; count];
        let mut spaces = HashMap::new();
        for (i, si) in simples.iter().enumerate() {
            for (j, sj) in simples.iter().enumerate() {
                for (k, slot) in dims[i][j].iter_mut().enumerate() {
                    *slot = ext_dim(si, sj, k).unwrap();
                    if *slot > 0 {
                        spaces.insert((i, j, k), ExtSpace::new(si, sj, k).unwrap());
                    }
                }
            }
        }
        SimpleExt {
            simples,
            dims,
            spaces,
        }
    }

    fn space(&self, i: usize, j: usize, k: usize) -> &ExtSpace {
        &self.spaces[&(i, j, k)]
    }

    fn basis(&self, i: usize, j: usize, k: usize) -> Vec<ExtClass> {
        let space = self.space(i, j, k);
        (0..space.dim()).map(|b| basis_class(space, b)).collect()
    }
}

/// The tier-1 fixtures with their Ext data, built once for the whole binary.
/// Five tests read the same list, and `SimpleExt::new` on the 5-vertex
/// `inhomogeneous-f5` builds 25 `ExtSpace` values per degree.
fn tier1_ext() -> &'static [(&'static str, Arc<Algebra>, SimpleExt)] {
    static CACHE: OnceLock<Vec<(&'static str, Arc<Algebra>, SimpleExt)>> = OnceLock::new();
    CACHE.get_or_init(|| {
        tier1_fixtures()
            .into_iter()
            .map(|(name, algebra)| {
                let ext = SimpleExt::new(&algebra);
                (name, algebra, ext)
            })
            .collect()
    })
}

/// The tier-2 domains with their AR quivers, built once for the whole binary.
/// Three tests read the same list, and the quiver carries the catalog the
/// catalog route needs.
fn tier2_ar() -> &'static [(&'static str, Arc<Algebra>, ArQuiver)] {
    static CACHE: OnceLock<Vec<(&'static str, Arc<Algebra>, ArQuiver)>> = OnceLock::new();
    CACHE.get_or_init(|| {
        tier2_domains()
            .into_iter()
            .map(|(name, algebra)| {
                let quiver = ar_quiver(&algebra).unwrap();
                (name, algebra, quiver)
            })
            .collect()
    })
}

/// The entrywise sum of two parallel morphisms. A sum of A-linear maps is
/// A-linear, so the checked constructor accepts it.
fn add_morphisms(f: &Morphism, g: &Morphism) -> Morphism {
    let field = f.source().field();
    let nv = f.source().algebra().quiver().num_vertices();
    let maps = (0..nv)
        .map(|v| f.map_at(v).add(g.map_at(v), &field))
        .collect();
    Morphism::new(f.source(), f.target(), maps).unwrap()
}

/// Krull-Schmidt classes of a middle term as sorted
/// (dimension vector, multiplicity) pairs.
fn middle_classes(middle: &Module) -> Vec<(Vec<usize>, usize)> {
    match krull_schmidt(middle) {
        KrullSchmidtOutcome::Classes(classes) => {
            let mut dims: Vec<(Vec<usize>, usize)> = classes
                .iter()
                .map(|c| (c.representative.dim_vector().to_vec(), c.multiplicity))
                .collect();
            dims.sort();
            dims
        }
        KrullSchmidtOutcome::Unknown { reason } => panic!("krull_schmidt failed: {reason}"),
    }
}

/// Nonzero coboundary cocycles of `space`, found through the public
/// surface alone. [`HomSpace`] spans the degree-`k` cochains,
/// `class_from_cocycle` either classifies a cocycle or carries the nonzero
/// composite of a non-cocycle, the cocycles are the kernel of the composite
/// matrix, and a coboundary is a cocycle whose class is zero.
fn coboundaries(space: &ExtSpace) -> Vec<Morphism> {
    let field = space.source().field();
    let hs = HomSpace::new(space.cochain_term(), space.target()).unwrap();
    if hs.dim() == 0 {
        return Vec::new();
    }
    let mut delta_rows: Vec<Option<Vec<Fp>>> = Vec::new();
    for h in hs.basis() {
        match space.class_from_cocycle(h) {
            Ok(_) => delta_rows.push(None),
            Err(ExtClassError::NotCocycle { composite }) => delta_rows.push(Some(composite)),
            Err(other) => panic!("a hom basis element was rejected for another reason: {other:?}"),
        }
    }
    let width = delta_rows
        .iter()
        .flatten()
        .map(Vec::len)
        .next()
        .unwrap_or(0);
    let cocycle_coords = if width == 0 {
        DenseMat::identity(hs.dim())
    } else {
        let rows: Vec<Vec<Fp>> = delta_rows
            .iter()
            .map(|r| r.clone().unwrap_or_else(|| vec![field.zero(); width]))
            .collect();
        DenseMat::from_rows(&rows).transpose().kernel_basis(&field)
    };
    let class_rows: Vec<Vec<Fp>> = (0..cocycle_coords.rows())
        .map(|r| {
            let z = hs.morphism(cocycle_coords.row(r));
            space
                .class_from_cocycle(&z)
                .expect("a kernel combination is a cocycle")
                .coordinates()
                .to_vec()
        })
        .collect();
    let zero_class_coeffs = if cocycle_coords.rows() == 0 {
        DenseMat::zero(0, 0)
    } else if space.dim() == 0 {
        DenseMat::identity(cocycle_coords.rows())
    } else {
        DenseMat::from_rows(&class_rows)
            .transpose()
            .kernel_basis(&field)
    };
    let mut boundaries = Vec::new();
    for r in 0..zero_class_coeffs.rows() {
        let mut coords = vec![field.zero(); hs.dim()];
        for (j, &c) in zero_class_coeffs.row(r).iter().enumerate() {
            for (slot, &z) in coords.iter_mut().zip(cocycle_coords.row(j)) {
                *slot = field.add(*slot, field.mul(c, z));
            }
        }
        let b = hs.morphism(&coords);
        if !b.is_zero() {
            boundaries.push(b);
        }
    }
    boundaries
}

#[test]
fn ext_space_dims_match_ext_dim_between_all_simples_and_hom_dim_at_degree_0() {
    for (name, algebra) in tier1_fixtures() {
        let n = algebra.quiver().num_vertices();
        let simples: Vec<Module> = (0..n).map(|v| Module::simple(&algebra, v)).collect();
        for (i, si) in simples.iter().enumerate() {
            for (j, sj) in simples.iter().enumerate() {
                for k in 0..=MAX_DEGREE {
                    let space = ExtSpace::new(si, sj, k).unwrap();
                    assert_eq!(
                        space.dim(),
                        ext_dim(si, sj, k).unwrap(),
                        "{name}: Ext^{k}(S_{i}, S_{j})"
                    );
                    if k == 0 {
                        assert_eq!(
                            space.dim(),
                            hom_dim(si, sj).unwrap(),
                            "{name}: Ext^0(S_{i}, S_{j}) vs Hom"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn identity_classes_are_two_sided_units_on_every_nonzero_bounded_space() {
    for (name, _, ext) in tier1_ext() {
        let n = ext.simples.len();
        for i in 0..n {
            for j in 0..n {
                for k in 0..=MAX_DEGREE {
                    if ext.dims[i][j][k] == 0 {
                        continue;
                    }
                    let id_left = ext.space(i, i, 0).identity_class().unwrap();
                    let id_right = ext.space(j, j, 0).identity_class().unwrap();
                    for (b, alpha) in ext.basis(i, j, k).iter().enumerate() {
                        assert!(
                            id_left.then(alpha).unwrap().equals(alpha).unwrap(),
                            "{name}: left unit on Ext^{k}(S_{i}, S_{j}) basis {b}"
                        );
                        assert!(
                            alpha.then(&id_right).unwrap().equals(alpha).unwrap(),
                            "{name}: right unit on Ext^{k}(S_{i}, S_{j}) basis {b}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn yoneda_products_are_bilinear_on_every_bounded_basis_pair() {
    for (name, _, ext) in tier1_ext() {
        let field = ext.simples[0].field();
        let two = field.elem(2);
        let n = ext.simples.len();
        let mut checked = 0usize;
        for i in 0..n {
            for j in 0..n {
                for l in 0..n {
                    for m in 0..=MAX_DEGREE {
                        for d in 0..=(MAX_DEGREE - m) {
                            if ext.dims[i][j][m] == 0 || ext.dims[j][l][d] == 0 {
                                continue;
                            }
                            let a_basis = ext.basis(i, j, m);
                            let b_basis = ext.basis(j, l, d);
                            let at =
                                format!("{name}: Ext^{m}(S_{i}, S_{j}) x Ext^{d}(S_{j}, S_{l})");
                            for u in &a_basis {
                                for v in &b_basis {
                                    let product = u.then(v).unwrap();
                                    assert_eq!(
                                        product.space().dim(),
                                        ext.dims[i][l][m + d],
                                        "{at}: product space dimension"
                                    );
                                    assert!(
                                        u.scale(two)
                                            .then(v)
                                            .unwrap()
                                            .equals(&product.scale(two))
                                            .unwrap(),
                                        "{at}: left scaling"
                                    );
                                    assert!(
                                        u.then(&v.scale(two))
                                            .unwrap()
                                            .equals(&product.scale(two))
                                            .unwrap(),
                                        "{at}: right scaling"
                                    );
                                    assert!(
                                        u.neg().then(v).unwrap().equals(&product.neg()).unwrap(),
                                        "{at}: negation"
                                    );
                                    checked += 1;
                                }
                            }
                            for u1 in &a_basis {
                                for u2 in &a_basis {
                                    for v in &b_basis {
                                        let left = u1.add(u2).unwrap().then(v).unwrap();
                                        let right =
                                            u1.then(v).unwrap().add(&u2.then(v).unwrap()).unwrap();
                                        assert!(
                                            left.equals(&right).unwrap(),
                                            "{at}: additivity in the left factor"
                                        );
                                    }
                                }
                            }
                            for u in &a_basis {
                                for v1 in &b_basis {
                                    for v2 in &b_basis {
                                        let left = u.then(&v1.add(v2).unwrap()).unwrap();
                                        let right =
                                            u.then(v1).unwrap().add(&u.then(v2).unwrap()).unwrap();
                                        assert!(
                                            left.equals(&right).unwrap(),
                                            "{at}: additivity in the right factor"
                                        );
                                    }
                                }
                            }
                            let a_space = ext.space(i, j, m);
                            let b_space = ext.space(j, l, d);
                            assert!(
                                a_space.zero_class().then(&b_basis[0]).unwrap().is_zero(),
                                "{at}: the zero class annihilates on the left"
                            );
                            assert!(
                                a_basis[0].then(&b_space.zero_class()).unwrap().is_zero(),
                                "{at}: the zero class annihilates on the right"
                            );
                        }
                    }
                }
            }
        }
        assert!(
            checked > 0,
            "{name}: the bounded range contains composable nonzero pairs"
        );
    }
}

#[test]
fn yoneda_products_are_associative_on_every_bounded_basis_triple() {
    for (name, _, ext) in tier1_ext() {
        let n = ext.simples.len();
        let mut checked = 0usize;
        for i in 0..n {
            for j in 0..n {
                for l in 0..n {
                    for q in 0..n {
                        for m in 0..=MAX_DEGREE {
                            for d in 0..=(MAX_DEGREE - m) {
                                for p in 0..=(MAX_DEGREE - m - d) {
                                    if ext.dims[i][j][m] == 0
                                        || ext.dims[j][l][d] == 0
                                        || ext.dims[l][q][p] == 0
                                    {
                                        continue;
                                    }
                                    for u in &ext.basis(i, j, m) {
                                        for v in &ext.basis(j, l, d) {
                                            for w in &ext.basis(l, q, p) {
                                                let left = u.then(v).unwrap().then(w).unwrap();
                                                let right = u.then(&v.then(w).unwrap()).unwrap();
                                                assert!(
                                                    left.equals(&right).unwrap(),
                                                    "{name}: associativity on degrees \
                                                     ({m}, {d}, {p}) at (S_{i}, S_{j}, \
                                                     S_{l}, S_{q})"
                                                );
                                                checked += 1;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        assert!(
            checked > 0,
            "{name}: the bounded range contains composable nonzero triples"
        );
    }
}

// Over A = k[x]/(x^3) with R = rad P = A/(x^2): the minimal resolution of
// S has d_1 = right multiplication by x and d_2 = right multiplication by
// x^2. Hom(P, R) has dimension 2, delta^0 sends f to f(1) x with image R x
// of dimension 1, and delta^1 sends f to f(1) x^2 = 0 in A/(x^2). So
// B^1(S, R) has dimension 1, Z^1 = Hom(P, R), and Ext^1(S, R) has
// dimension 1. Ext^1(R, S) also has dimension 1: the resolution of R
// swaps the two differentials and both compose to zero into S. The counts
// are characteristic free, so both fields run.
//
// This test works at the class level: it reduces the shifted cocycle to
// its class and multiplies the class, so the product construction only
// ever sees the canonical representative. The representative-level gate,
// which runs the lift construction on the altered cocycle itself, is the
// ext.rs unit test
// `a_left_cocycle_shifted_by_a_coboundary_lifts_to_the_same_product` (and
// its right-factor sibling).
#[test]
fn a_shifted_cocycle_recovers_its_class_and_the_class_product_is_unchanged() {
    for field in [f2(), f5()] {
        let algebra = truncated_poly(3, field).unwrap();
        let s = Module::simple(&algebra, 0);
        let r = radical(&Module::projective(&algebra, 0)).0;
        let left = ExtSpace::new(&s, &r, 1).unwrap();
        let right = ExtSpace::new(&r, &s, 1).unwrap();
        assert_eq!(left.dim(), 1, "Ext^1(S, R) over F_{}", field.modulus());
        assert_eq!(right.dim(), 1, "Ext^1(R, S) over F_{}", field.modulus());
        let alpha = basis_class(&left, 0);
        let beta = basis_class(&right, 0);
        let product = alpha.then(&beta).unwrap();
        let shifts = coboundaries(&left);
        assert!(
            !shifts.is_empty(),
            "B^1(S, R) is nonzero by the derivation above"
        );
        for b in &shifts {
            let shifted = add_morphisms(&alpha.representative(), b);
            let recovered = left.class_from_cocycle(&shifted).unwrap();
            assert!(
                recovered.equals(&alpha).unwrap(),
                "the shifted cocycle keeps its class over F_{}",
                field.modulus()
            );
            assert!(
                recovered.then(&beta).unwrap().equals(&product).unwrap(),
                "the shifted cocycle keeps its product over F_{}",
                field.modulus()
            );
        }
    }
}

// Class level only: recovery round-trips each factor through its
// extension and multiplies the recovered classes, which equal the
// original classes, so both products run the same construction. The
// gate that recovers the pre-reduction connecting cocycle from the
// extension object and splices it independently is the ext.rs unit test
// `the_cocycle_recovered_from_the_extension_splices_to_the_product`.
#[test]
fn ext1_class_recovery_round_trips_and_the_recovered_classes_compose_alike() {
    for (name, _, ext) in tier1_ext() {
        let n = ext.simples.len();
        let mut checked = 0usize;
        for i in 0..n {
            for j in 0..n {
                for l in 0..n {
                    if ext.dims[i][j][1] == 0 || ext.dims[j][l][1] == 0 {
                        continue;
                    }
                    let a_space = ext.space(i, j, 1);
                    let b_space = ext.space(j, l, 1);
                    for alpha in &ext.basis(i, j, 1) {
                        for beta in &ext.basis(j, l, 1) {
                            let ses_a = ShortExactSequence::from_ext1(alpha).unwrap();
                            let ses_b = ShortExactSequence::from_ext1(beta).unwrap();
                            let recovered_a = ses_a.ext1_class(a_space).unwrap();
                            let recovered_b = ses_b.ext1_class(b_space).unwrap();
                            assert!(recovered_a.equals(alpha).unwrap(), "{name}: left recovery");
                            assert!(recovered_b.equals(beta).unwrap(), "{name}: right recovery");
                            // The recovered classes equal the originals,
                            // so this checks that recovery feeds the
                            // product construction unchanged, not the
                            // splice itself; see the ext.rs gate above.
                            let direct = alpha.then(beta).unwrap();
                            let via_recovery = recovered_a.then(&recovered_b).unwrap();
                            assert!(
                                via_recovery.equals(&direct).unwrap(),
                                "{name}: recovered-class product at (S_{i}, S_{j}, S_{l})"
                            );
                            assert_eq!(
                                direct.space().dim(),
                                ext.dims[i][l][2],
                                "{name}: product dimension at (S_{i}, S_{l})"
                            );
                            checked += 1;
                        }
                    }
                }
            }
        }
        assert!(checked > 0, "{name}: some Ext^1 pair composes");
    }
}

#[test]
fn from_ext1_round_trips_every_basis_class_and_split_status_matches_is_zero() {
    for (name, algebra, ext) in tier1_ext() {
        let nv = algebra.quiver().num_vertices();
        let n = ext.simples.len();
        for i in 0..n {
            for j in 0..n {
                if ext.dims[i][j][1] == 0 {
                    continue;
                }
                let space = ext.space(i, j, 1);
                for (b, class) in ext.basis(i, j, 1).iter().enumerate() {
                    let ses = ShortExactSequence::from_ext1(class).unwrap();
                    assert!(ses.quotient().ptr_eq(space.source()), "{name}: quotient");
                    assert!(ses.sub().ptr_eq(space.target()), "{name}: sub");
                    for v in 0..nv {
                        assert_eq!(
                            ses.middle().dim_at(v),
                            ses.sub().dim_at(v) + ses.quotient().dim_at(v),
                            "{name}: dimensions at vertex {v} for Ext^1(S_{i}, S_{j}) basis {b}"
                        );
                    }
                    let recovered = ses.ext1_class(space).unwrap();
                    assert!(
                        recovered.equals(class).unwrap(),
                        "{name}: round trip of Ext^1(S_{i}, S_{j}) basis {b}"
                    );
                    // A basis class is nonzero, so the sequence must not
                    // split: a split sequence recovers the zero class.
                    match ses.split_status() {
                        SplitStatus::NonSplit(witness) => assert!(
                            witness.verify(&ses),
                            "{name}: non-split witness for basis {b}"
                        ),
                        SplitStatus::Split(_) => {
                            panic!("{name}: the nonzero basis class {b} split")
                        }
                    }
                }
                let ses = ShortExactSequence::from_ext1(&space.zero_class()).unwrap();
                assert!(
                    ses.ext1_class(space).unwrap().is_zero(),
                    "{name}: the zero class recovers zero"
                );
                match ses.split_status() {
                    SplitStatus::Split(witness) => assert!(
                        witness.verify(&ses),
                        "{name}: split witness for the zero class"
                    ),
                    SplitStatus::NonSplit(_) => {
                        panic!("{name}: the zero class of Ext^1(S_{i}, S_{j}) did not split")
                    }
                }
            }
        }
    }
}

#[test]
fn almost_split_runs_on_every_simple_with_a_verifying_duality_witness() {
    for (name, algebra) in tier1_fixtures() {
        let nv = algebra.quiver().num_vertices();
        for v in 0..nv {
            let s = Module::simple(&algebra, v);
            let ind = IndecomposableModule::new(&s).unwrap();
            match almost_split(&ind).unwrap() {
                AlmostSplitOutcome::Projective => {
                    assert!(ind.is_projective(), "{name}: S_{v} projective outcome");
                    assert!(tau(&s).unwrap().is_zero(), "{name}: tau S_{v} is zero");
                }
                AlmostSplitOutcome::Sequence(sequence) => {
                    assert!(!ind.is_projective(), "{name}: S_{v} sequence outcome");
                    let ses = sequence.sequence();
                    assert!(ses.quotient().ptr_eq(&s), "{name}: S_{v} ends its sequence");
                    for w in 0..nv {
                        assert_eq!(
                            ses.middle().dim_at(w),
                            ses.sub().dim_at(w) + ses.quotient().dim_at(w),
                            "{name}: dim tau S_{v} + dim S_{v} = dim middle at vertex {w}"
                        );
                    }
                    let witness = duality_witness(&sequence);
                    assert!(
                        witness.verify(&ind, ses, sequence.chosen_ar_class()),
                        "{name}: duality witness for S_{v}"
                    );
                    // The standalone translate route must agree with the
                    // sub term, matrix for matrix: tau is deterministic.
                    let translate = tau(&s).unwrap();
                    assert!(
                        !translate.is_zero(),
                        "{name}: tau S_{v} is zero for a non-projective simple"
                    );
                    assert_eq!(
                        translate.dim_vector(),
                        ses.sub().dim_vector(),
                        "{name}: tau route dimension for S_{v}"
                    );
                    for a in 0..algebra.quiver().num_arrows() {
                        let arrow = ArrowId(a as u32);
                        assert_eq!(
                            translate.map(arrow).entries_u64(),
                            ses.sub().map(arrow).entries_u64(),
                            "{name}: tau route matrices for S_{v} at arrow {a}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn almost_split_terms_match_the_hand_derived_values() {
    // Commutative square over F_5, by the AR formula derivation of
    // tests/acceptance_nonmonomial.rs row 9: tau S_0 = [1, 1, 1, 0],
    // tau S_1 = [0, 0, 1, 1], tau S_2 = [0, 1, 0, 1], and S_3 = P_3 is
    // projective.
    let square = commutative_square(f5());
    let expected: [&[usize]; 3] = [&[1, 1, 1, 0], &[0, 0, 1, 1], &[0, 1, 0, 1]];
    for (v, sub_dims) in expected.iter().enumerate() {
        let ind = IndecomposableModule::new(&Module::simple(&square, v as u32)).unwrap();
        let sequence = duality_sequence(&ind);
        assert_eq!(
            sequence.sequence().sub().dim_vector(),
            *sub_dims,
            "square: tau S_{v}"
        );
    }
    let p3 = IndecomposableModule::new(&Module::simple(&square, 3)).unwrap();
    assert!(matches!(
        almost_split(&p3).unwrap(),
        AlmostSplitOutcome::Projective
    ));

    // Preprojective A_3 over F_2 is self-injective, so no simple is
    // projective. The translate dimension vectors are the QPA-verified
    // values of tests/acceptance_nonmonomial.rs row 9.
    let b = preprojective_a3();
    let expected: [&[usize]; 3] = [&[0, 1, 1], &[1, 1, 1], &[1, 1, 0]];
    for (v, sub_dims) in expected.iter().enumerate() {
        let ind = IndecomposableModule::new(&Module::simple(&b, v as u32)).unwrap();
        let sequence = duality_sequence(&ind);
        assert_eq!(
            sequence.sequence().sub().dim_vector(),
            *sub_dims,
            "preprojective: tau S_{v}"
        );
    }

    // Linear A_3 over F_5: Hom between interval modules is at most one
    // line, and the hand-derived zigzag AR quiver gives the meshes
    // 0 -> S_1 -> I_1 -> S_0 -> 0 and 0 -> S_2 -> P_1 -> S_1 -> 0.
    let a3 = linear_an(3, f5());
    let s0 = IndecomposableModule::new(&Module::simple(&a3, 0)).unwrap();
    let sequence = duality_sequence(&s0);
    assert_eq!(sequence.sequence().sub().dim_vector(), &[0, 1, 0]);
    assert_eq!(sequence.sequence().middle().dim_vector(), &[1, 1, 0]);
    let s1 = IndecomposableModule::new(&Module::simple(&a3, 1)).unwrap();
    let sequence = duality_sequence(&s1);
    assert_eq!(sequence.sequence().sub().dim_vector(), &[0, 0, 1]);
    assert_eq!(sequence.sequence().middle().dim_vector(), &[0, 1, 1]);
    let s2 = IndecomposableModule::new(&Module::simple(&a3, 2)).unwrap();
    assert!(matches!(
        almost_split(&s2).unwrap(),
        AlmostSplitOutcome::Projective
    ));

    // k[x]/(x^n) is symmetric, so tau S = Omega^2 S = S, and the unique
    // non-split self-extension of S is the uniserial module of dimension
    // 2: the sequence is 0 -> S -> rad P -> S -> 0 over both fields.
    for field in [f2(), f5()] {
        let x3 = truncated_poly(3, field).unwrap();
        let s = IndecomposableModule::new(&Module::simple(&x3, 0)).unwrap();
        let sequence = duality_sequence(&s);
        assert_eq!(sequence.sequence().sub().dim_vector(), &[1]);
        assert_eq!(sequence.sequence().middle().dim_vector(), &[2]);
        assert_eq!(sequence.sequence().quotient().dim_vector(), &[1]);
    }
}

#[test]
fn stable_hom_dimensions_are_consistent_everywhere() {
    for (name, algebra) in tier1_fixtures() {
        let nv = algebra.quiver().num_vertices();
        // The identity of a projective factors through its own cover, so
        // its stable endomorphism space is zero.
        for v in 0..nv {
            let p = Module::projective(&algebra, v);
            assert_eq!(
                stable_end(&p).unwrap().dim(),
                0,
                "{name}: stable End(P_{v})"
            );
        }
        let mut family: Vec<Module> = (0..nv).map(|v| Module::simple(&algebra, v)).collect();
        family.extend((0..nv).map(|v| Module::projective(&algebra, v)));
        for m in &family {
            for target in &family {
                assert!(
                    stable_hom(m, target).unwrap().dim() <= hom_dim(m, target).unwrap(),
                    "{name}: stable Hom({:?}, {:?}) exceeds Hom",
                    m.dim_vector(),
                    target.dim_vector()
                );
            }
        }
    }
}

// The cross-check gate of design section 12: for every non-projective
// catalog vertex M, the Krull-Schmidt multiplicities of the middle term of
// its almost-split sequence equal the over_source_residue values of the
// arrows into M.
#[test]
fn middle_term_multiplicities_match_the_arrows_into_each_vertex() {
    for (name, _, quiver) in tier2_ar() {
        let dims: Vec<Vec<usize>> = quiver
            .vertices()
            .iter()
            .map(|v| v.module().module().dim_vector().to_vec())
            .collect();
        // Dimension vectors identify catalog entries on these domains, so
        // Krull-Schmidt classes match arrows by dimension vector alone.
        for (a, da) in dims.iter().enumerate() {
            for db in dims.iter().skip(a + 1) {
                assert_ne!(da, db, "{name}: catalog dimension vectors are distinct");
            }
        }
        let mut checked = 0usize;
        for vertex in quiver.vertices() {
            if vertex.projective() {
                continue;
            }
            let sequence = duality_sequence(vertex.module());
            let mut expected: Vec<(Vec<usize>, usize)> = quiver
                .arrows()
                .iter()
                .filter(|arrow| arrow.target() == vertex.id())
                .map(|arrow| (dims[arrow.source()].clone(), arrow.over_source_residue()))
                .collect();
            expected.sort();
            assert_eq!(
                middle_classes(sequence.sequence().middle()),
                expected,
                "{name}: middle term of vertex {} ({:?})",
                vertex.id(),
                dims[vertex.id()]
            );
            checked += 1;
        }
        assert!(
            checked > 0,
            "{name}: the domain has non-projective vertices"
        );
    }
}

#[test]
fn the_catalog_route_agrees_with_the_duality_route_on_every_vertex() {
    for (name, _, quiver) in tier2_ar() {
        let catalog = quiver.catalog();
        for vertex in quiver.vertices() {
            if vertex.projective() {
                continue;
            }
            let duality = duality_sequence(vertex.module());
            let via = catalog_sequence(vertex.module(), catalog);
            assert_eq!(
                duality.sequence().middle().dim_vector(),
                via.sequence().middle().dim_vector(),
                "{name}: middle terms of vertex {}",
                vertex.id()
            );
            // tau is deterministic, so both routes compute identical Ext
            // bases and class coordinates transport verbatim.
            let transported = duality
                .chosen_ar_class()
                .space()
                .class_from_coordinates(via.chosen_ar_class().coordinates())
                .unwrap();
            assert!(
                transported.equals(duality.chosen_ar_class()).unwrap(),
                "{name}: chosen classes of vertex {}",
                vertex.id()
            );
            let witness = catalog_witness(&via);
            assert!(
                witness.verify(
                    vertex.module(),
                    catalog,
                    via.sequence(),
                    via.chosen_ar_class()
                ),
                "{name}: catalog witness of vertex {}",
                vertex.id()
            );
            let dual_witness = duality_witness(&duality);
            assert!(
                dual_witness.verify(
                    vertex.module(),
                    duality.sequence(),
                    duality.chosen_ar_class()
                ),
                "{name}: duality witness of vertex {}",
                vertex.id()
            );
        }
    }
}

// Every indecomposable on the v0.4 catalog domains has
// End(M)/rad End(M) = k, so every residue degree is 1 and every arrow
// valuation is plain.
#[test]
fn every_arrow_valuation_on_the_catalog_domains_is_plain() {
    for (name, _, quiver) in tier2_ar() {
        for vertex in quiver.vertices() {
            assert_eq!(
                vertex.residue_degree(),
                1,
                "{name}: residue degree of vertex {}",
                vertex.id()
            );
        }
        for arrow in quiver.arrows() {
            assert_eq!(
                arrow.valuation(),
                ArrowValuation::Plain(arrow.base_dim()),
                "{name}: valuation of arrow {} -> {}",
                arrow.source(),
                arrow.target()
            );
        }
    }
}

// Tier separation of design section 18: the preprojective algebra of A_3
// is representation finite, but this release certifies no catalog for it,
// so tier 1 covers it (the almost_split tests above) while the AR quiver
// dispatch rejects it with both reasons.
#[test]
fn preprojective_a3_runs_tier_1_only_and_ar_quiver_carries_both_rejections() {
    let algebra = preprojective_a3();
    match ar_quiver(&algebra).unwrap_err() {
        ArQuiverError::UnsupportedDomain { dynkin, nakayama } => {
            // The completed reduced Groebner basis has five elements: the
            // three input relations plus the two productive completions
            // a.b.bbar and b.bbar.abar of acceptance_nonmonomial.rs.
            assert_eq!(dynkin, DynkinError::NonzeroIdeal { relations: 5 });
            // Vertex 1 carries the arrows b and abar out and a and bbar in.
            assert_eq!(
                nakayama,
                EnumerateError::NotNakayama {
                    vertex: 1,
                    incoming: 2,
                    outgoing: 2,
                }
            );
        }
        other => panic!("expected UnsupportedDomain, got {other:?}"),
    }
}
