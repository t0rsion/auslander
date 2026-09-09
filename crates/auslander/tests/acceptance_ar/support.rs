use std::collections::HashMap;
use std::sync::{Arc, OnceLock};

use auslander::algebra::{
    Algebra, commutative_square, linear_an, path_algebra, radical_square_zero_cycle, truncated_poly,
};
use auslander::arquiver::ArQuiver;
use auslander::decompose::{KrullSchmidtOutcome, krull_schmidt};
use auslander::dynkin::{DynkinType, dynkin_quiver};
use auslander::ext::{ExtClass, ExtClassError, ExtSpace, ext_dim};
use auslander::field::{Fp, PrimeField};
use auslander::hom::Morphism;
use auslander::homspace::HomSpace;
use auslander::linalg::DenseMat;
use auslander::module::Module;

use crate::common::{basis_class, f2, f5, inhomogeneous, preprojective_a3};

/// Products run on every basis tuple whose degrees sum to at most this.
pub(crate) const MAX_DEGREE: usize = 3;

pub(crate) fn tier1_fixtures() -> Vec<(&'static str, Arc<Algebra>)> {
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
pub(crate) struct SimpleExt {
    pub(crate) simples: Vec<Module>,
    pub(crate) dims: Vec<Vec<Vec<usize>>>,
    spaces: HashMap<(usize, usize, usize), ExtSpace>,
}

impl SimpleExt {
    pub(crate) fn new(algebra: &Arc<Algebra>) -> SimpleExt {
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

    pub(crate) fn space(&self, i: usize, j: usize, k: usize) -> &ExtSpace {
        &self.spaces[&(i, j, k)]
    }

    pub(crate) fn basis(&self, i: usize, j: usize, k: usize) -> Vec<ExtClass> {
        let space = self.space(i, j, k);
        (0..space.dim()).map(|b| basis_class(space, b)).collect()
    }
}

/// The tier-1 fixtures with their Ext data, built once for the whole binary.
/// Five tests read the same list, and `SimpleExt::new` on the 5-vertex
/// `inhomogeneous-f5` builds 25 `ExtSpace` values per degree.
pub(crate) fn tier1_ext() -> &'static [(&'static str, Arc<Algebra>, SimpleExt)] {
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
pub(crate) fn tier2_ar() -> &'static [(&'static str, Arc<Algebra>, ArQuiver)] {
    static CACHE: OnceLock<Vec<(&'static str, Arc<Algebra>, ArQuiver)>> = OnceLock::new();
    CACHE.get_or_init(|| {
        tier2_domains()
            .into_iter()
            .map(|(name, algebra)| {
                let quiver = auslander::arquiver::ar_quiver(&algebra).unwrap();
                (name, algebra, quiver)
            })
            .collect()
    })
}

/// The entrywise sum of two parallel morphisms. A sum of A-linear maps is
/// A-linear, so the checked constructor accepts it.
pub(crate) fn add_morphisms(f: &Morphism, g: &Morphism) -> Morphism {
    let field = f.source().field();
    let nv = f.source().algebra().quiver().num_vertices();
    let maps = (0..nv)
        .map(|v| f.map_at(v).add(g.map_at(v), &field))
        .collect();
    Morphism::new(f.source(), f.target(), maps).unwrap()
}

/// Krull-Schmidt classes of a middle term as sorted
/// (dimension vector, multiplicity) pairs.
pub(crate) fn middle_classes(middle: &Module) -> Vec<(Vec<usize>, usize)> {
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

fn cocycle_coordinates(space: &ExtSpace, hom: &HomSpace) -> DenseMat {
    let field = space.source().field();
    let mut delta_rows: Vec<Option<Vec<Fp>>> = Vec::new();
    for basis in hom.basis() {
        match space.class_from_cocycle(basis) {
            Ok(_) => delta_rows.push(None),
            Err(ExtClassError::NotCocycle { composite }) => delta_rows.push(Some(composite)),
            Err(other) => panic!("a hom basis element was rejected: {other:?}"),
        }
    }
    let width = delta_rows
        .iter()
        .flatten()
        .map(Vec::len)
        .next()
        .unwrap_or(0);
    if width == 0 {
        return DenseMat::identity(hom.dim());
    }
    let rows: Vec<Vec<Fp>> = delta_rows
        .iter()
        .map(|row| row.clone().unwrap_or_else(|| vec![field.zero(); width]))
        .collect();
    DenseMat::from_rows(&rows).transpose().kernel_basis(&field)
}

fn zero_class_coordinates(space: &ExtSpace, hom: &HomSpace, cocycles: &DenseMat) -> DenseMat {
    if cocycles.rows() == 0 {
        return DenseMat::zero(0, 0);
    }
    if space.dim() == 0 {
        return DenseMat::identity(cocycles.rows());
    }
    let rows: Vec<Vec<Fp>> = (0..cocycles.rows())
        .map(|row| {
            space
                .class_from_cocycle(&hom.morphism(cocycles.row(row)))
                .expect("a kernel combination is a cocycle")
                .coordinates()
                .to_vec()
        })
        .collect();
    DenseMat::from_rows(&rows)
        .transpose()
        .kernel_basis(&space.source().field())
}

fn boundary_morphism(hom: &HomSpace, cocycles: &DenseMat, coefficients: &[Fp]) -> Morphism {
    let field = hom.source().field();
    let mut coordinates = vec![field.zero(); hom.dim()];
    for (index, &coefficient) in coefficients.iter().enumerate() {
        for (slot, &value) in coordinates.iter_mut().zip(cocycles.row(index)) {
            *slot = field.add(*slot, field.mul(coefficient, value));
        }
    }
    hom.morphism(&coordinates)
}

/// Nonzero coboundary cocycles of `space`, found through the public
/// surface alone. [`HomSpace`] spans the degree-`k` cochains,
/// `class_from_cocycle` either classifies a cocycle or carries the nonzero
/// composite of a non-cocycle, the cocycles are the kernel of the composite
/// matrix, and a coboundary is a cocycle whose class is zero.
pub(crate) fn coboundaries(space: &ExtSpace) -> Vec<Morphism> {
    let hom = HomSpace::new(space.cochain_term(), space.target()).unwrap();
    if hom.dim() == 0 {
        return Vec::new();
    }
    let cocycles = cocycle_coordinates(space, &hom);
    let zero_classes = zero_class_coordinates(space, &hom, &cocycles);
    let mut boundaries = Vec::new();
    for row in 0..zero_classes.rows() {
        let boundary = boundary_morphism(&hom, &cocycles, zero_classes.row(row));
        if !boundary.is_zero() {
            boundaries.push(boundary);
        }
    }
    boundaries
}
