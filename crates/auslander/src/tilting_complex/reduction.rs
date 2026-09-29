use std::collections::BTreeMap;

use super::*;
use crate::decompose::{add_morphisms, direct_sum_or_zero, inverse_morphism};
use crate::hom::{identity, zero_morphism};
use crate::homotopy::{block_matrices, rebase_morphism};
use crate::homspace::scale_morphism;
use crate::perfect::ProjectiveTermWitness;

/// Morphisms between canonical projectives: `blocks[a][b]` runs from summand
/// `a` of one term to summand `b` of another.
type Blocks = Vec<Vec<Morphism>>;

/// Gaussian elimination state on the canonical-projective form of a complex.
///
/// `differentials[k]` runs from term `k + 1` to term `k`. `forward[k]` maps
/// the original summands of term `k` to its current summands, and
/// `backward[k]` maps the current summands back.
struct Elimination {
    projectives: Vec<Module>,
    vertices: Vec<Vec<u32>>,
    differentials: Vec<Blocks>,
    forward: Vec<Blocks>,
    backward: Vec<Blocks>,
}

fn subtract(left: &Morphism, right: &Morphism) -> Morphism {
    let field = left.source().field();
    add_morphisms(left, &scale_morphism(right, field.neg(field.one())))
}

/// Subtracts the product `left[i]·right[j]` from each `blocks[i][j]`.
fn subtract_product(
    blocks: &mut Blocks,
    left: &[Morphism],
    right: &[Morphism],
) -> Result<(), HomError> {
    for (maps, left) in blocks.iter_mut().zip(left) {
        for (map, right) in maps.iter_mut().zip(right) {
            *map = subtract(map, &left.then(right)?);
        }
    }
    Ok(())
}

fn identity_blocks(projectives: &[Module], vertices: &[u32]) -> Result<Blocks, HomError> {
    let module = |index: usize| &projectives[vertices[index] as usize];
    (0..vertices.len())
        .map(|row| {
            (0..vertices.len())
                .map(|column| {
                    if row == column {
                        Ok(identity(module(row)))
                    } else {
                        zero_morphism(module(row), module(column))
                    }
                })
                .collect()
        })
        .collect()
}

impl Elimination {
    fn new(complex: &ProjectiveComplex, meter: &mut WorkMeter) -> Result<Elimination, Interrupt> {
        let algebra = complex.complex().terms()[0].algebra();
        let projectives: Vec<Module> = (0..algebra.quiver().num_vertices())
            .map(|vertex| Module::projective(algebra, vertex))
            .collect();
        let vertices: Vec<Vec<u32>> = complex
            .terms()
            .iter()
            .map(|term| term.vertices().to_vec())
            .collect();
        let mut differentials = Vec::with_capacity(vertices.len().saturating_sub(1));
        for (offset, differential) in complex.complex().differentials().iter().enumerate() {
            meter.charge()?;
            let (source, target) = (&complex.terms()[offset + 1], &complex.terms()[offset]);
            differentials.push(component_blocks(
                &projectives,
                source,
                target,
                differential,
            )?);
        }
        let forward = vertices
            .iter()
            .map(|term| identity_blocks(&projectives, term))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Elimination {
            backward: forward.clone(),
            projectives,
            vertices,
            differentials,
            forward,
        })
    }

    /// The first differential component, in degree and summand order, that is
    /// an isomorphism of canonical projectives.
    fn pivot(&self) -> Option<(usize, usize, usize)> {
        self.differentials
            .iter()
            .enumerate()
            .find_map(|(offset, blocks)| {
                let (sources, targets) = (&self.vertices[offset + 1], &self.vertices[offset]);
                blocks.iter().enumerate().find_map(|(row, maps)| {
                    maps.iter()
                        .enumerate()
                        .find(|(column, map)| {
                            sources[row] == targets[*column] && map.is_isomorphism()
                        })
                        .map(|(column, _)| (offset, row, column))
                })
            })
    }

    /// Splits off the contractible summand `X → Y` of the pivot `φ` at
    /// differential `offset`.
    ///
    /// With `d = [φ, β; γ, δ]` from `X ⊕ B` to `Y ⊕ D`, the complex is
    /// isomorphic to `(X → Y) ⊕ C'`, where `C'` has differential
    /// `δ - γ·φ⁻¹·β` and keeps the other differentials restricted to `B` and
    /// `D`. The projection to `C'` is `π_B` on `X ⊕ B` and `π_D - π_Y·φ⁻¹·β`
    /// on `Y ⊕ D`. The inclusion is `ι_B - γ·φ⁻¹·ι_X` on `B` and `ι_D` on
    /// `D`. The inclusion followed by the projection is the identity.
    fn eliminate(&mut self, offset: usize, row: usize, column: usize) -> Result<(), HomError> {
        let blocks = &self.differentials[offset];
        let inverse = inverse_morphism(&blocks[row][column]).expect("the pivot is invertible");
        let gamma = blocks
            .iter()
            .map(|maps| maps[column].then(&inverse))
            .collect::<Result<Vec<_>, _>>()?;
        let pivot_row = blocks[row].clone();
        let beta = pivot_row
            .iter()
            .map(|map| inverse.then(map))
            .collect::<Result<Vec<_>, _>>()?;
        let backward_row = self.backward[offset + 1][row].clone();
        let forward_column: Vec<Morphism> = self.forward[offset]
            .iter()
            .map(|maps| maps[column].clone())
            .collect();
        subtract_product(&mut self.differentials[offset], &gamma, &pivot_row)?;
        subtract_product(&mut self.backward[offset + 1], &gamma, &backward_row)?;
        subtract_product(&mut self.forward[offset], &forward_column, &beta)?;
        self.remove(offset, row, column);
        Ok(())
    }

    /// Drops summand `row` of term `offset + 1` and summand `column` of term
    /// `offset` from every block matrix.
    fn remove(&mut self, offset: usize, row: usize, column: usize) {
        let drop_column = |blocks: &mut Blocks, column: usize| {
            blocks.iter_mut().for_each(|maps| {
                maps.remove(column);
            })
        };
        self.differentials[offset].remove(row);
        drop_column(&mut self.differentials[offset], column);
        if let Some(above) = self.differentials.get_mut(offset + 1) {
            drop_column(above, row);
        }
        if let Some(below) = offset.checked_sub(1) {
            self.differentials[below].remove(column);
        }
        drop_column(&mut self.forward[offset + 1], row);
        self.backward[offset + 1].remove(row);
        drop_column(&mut self.forward[offset], column);
        self.backward[offset].remove(column);
        self.vertices[offset + 1].remove(row);
        self.vertices[offset].remove(column);
    }

    fn parts(&self, vertices: &[u32]) -> Vec<Module> {
        vertices
            .iter()
            .map(|&vertex| self.projectives[vertex as usize].clone())
            .collect()
    }
}

fn component_blocks(
    projectives: &[Module],
    source: &ProjectiveTermWitness,
    target: &ProjectiveTermWitness,
    differential: &Morphism,
) -> Result<Blocks, HomError> {
    let split = (source.split(), target.split());
    source
        .vertices()
        .iter()
        .zip(split.0.inclusions())
        .map(|(&from, inclusion)| {
            let through = inclusion.then(differential)?;
            target
                .vertices()
                .iter()
                .zip(split.1.projections())
                .map(|(&to, projection)| {
                    let block = through.then(projection)?;
                    Ok(rebase_morphism(
                        &block,
                        &projectives[from as usize],
                        &projectives[to as usize],
                    ))
                })
                .collect()
        })
        .collect()
}

/// Assembles a block matrix between two ordered sums into one morphism.
fn assemble(
    source: (&Module, &[Module]),
    target: (&Module, &[Module]),
    blocks: &[Vec<Morphism>],
) -> Result<Morphism, HomError> {
    let placements: Vec<(usize, usize)> = (0..source.1.len())
        .flat_map(|row| (0..target.1.len()).map(move |column| (row, column)))
        .collect();
    let flat: Vec<Morphism> = blocks.iter().flatten().cloned().collect();
    let matrices = block_matrices(source.1, target.1, &flat, &placements, source.0, target.0);
    Morphism::new(source.0, target.0, matrices)
}

/// The inclusions of a term split as one row, or its projections as one
/// column, in the orientation `assemble` expects.
fn split_blocks(witness: &ProjectiveTermWitness, into_term: bool) -> Blocks {
    let split = witness.split();
    if into_term {
        split
            .inclusions()
            .iter()
            .map(|map| vec![map.clone()])
            .collect()
    } else {
        vec![split.projections().to_vec()]
    }
}

/// The terms, differentials, and chain map components of an eliminated
/// complex, over the full degree range of the original.
struct Assembled {
    sums: Vec<Module>,
    differentials: Vec<Morphism>,
    forward: Vec<Morphism>,
    backward: Vec<Morphism>,
}

fn assemble_elimination(
    complex: &ProjectiveComplex,
    state: &Elimination,
) -> Result<Assembled, HomError> {
    let algebra = complex.complex().terms()[0].algebra();
    let sums: Vec<(Module, Vec<Module>)> = state
        .vertices
        .iter()
        .map(|vertices| {
            let parts = state.parts(vertices);
            (direct_sum_or_zero(algebra, parts.iter()).0, parts)
        })
        .collect();
    let differentials = state
        .differentials
        .iter()
        .enumerate()
        .map(|(offset, blocks)| {
            let (source, target) = (&sums[offset + 1], &sums[offset]);
            assemble((&source.0, &source.1), (&target.0, &target.1), blocks)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut forward = Vec::with_capacity(sums.len());
    let mut backward = Vec::with_capacity(sums.len());
    for (offset, witness) in complex.terms().iter().enumerate() {
        let module = witness.module();
        let original = state.parts(witness.vertices());
        let canonical = direct_sum_or_zero(algebra, original.iter()).0;
        let summands = witness.split().summands();
        let (sum, parts) = (&sums[offset].0, &sums[offset].1[..]);
        let project = assemble(
            (module, std::slice::from_ref(module)),
            (&canonical, summands),
            &split_blocks(witness, false),
        )?;
        let include = assemble(
            (&canonical, summands),
            (module, std::slice::from_ref(module)),
            &split_blocks(witness, true),
        )?;
        let to_current = assemble(
            (&canonical, &original),
            (sum, parts),
            &state.forward[offset],
        )?;
        let from_current = assemble(
            (sum, parts),
            (&canonical, &original),
            &state.backward[offset],
        )?;
        forward.push(project.then(&to_current)?);
        backward.push(from_current.then(&include)?);
    }
    Ok(Assembled {
        sums: sums.into_iter().map(|(sum, _)| sum).collect(),
        differentials,
        forward,
        backward,
    })
}

/// The first and last offsets with a nonzero term.
fn support(terms: &[Module]) -> Option<(usize, usize)> {
    let first = terms.iter().position(|term| !term.is_zero())?;
    let last = terms.iter().rposition(|term| !term.is_zero())?;
    Some((first, last))
}

fn restricted(
    lower: i32,
    terms: &[Module],
    differentials: &[Morphism],
    (first, last): (usize, usize),
) -> Result<BoundedComplex, BoundedComplexError> {
    BoundedComplex::new(
        lower + first as i32,
        terms[first..=last].to_vec(),
        differentials[first..last].to_vec(),
    )
}

/// The nonzero homology dimension vectors by degree.
fn homology(complex: &BoundedComplex) -> Option<BTreeMap<i32, Vec<usize>>> {
    let checked = complex.to_checked().ok()?;
    let mut homology = BTreeMap::new();
    for index in 0..checked.len() {
        let dimensions = checked.homology_dimensions(index).ok()?;
        if !dimensions.is_zero() {
            let degree = complex.upper() - index as i32;
            homology.insert(degree, dimensions.dimension_vector().to_vec());
        }
    }
    Some(homology)
}

/// A checked homotopy equivalence from a projective complex to a minimal
/// complex.
///
/// Minimal means that no differential component between canonical
/// projective summands is an isomorphism, so every differential lands in the
/// radical. For bounded complexes of finitely generated projectives over a
/// finite-dimensional algebra, two minimal complexes are homotopy equivalent
/// exactly when they are isomorphic.
///
/// The proof obligation has two checked parts. First, `backward` followed by
/// `forward` is the identity of the minimal complex. Then `forward` followed
/// by `backward` is an idempotent chain endomorphism of the source, and the
/// source splits as the minimal complex plus a bounded complex `K` of
/// projectives. Second, both complexes have equal homology dimension vectors in
/// every degree, so `K` is acyclic. A bounded acyclic complex of projectives is
/// contractible, so `forward` and `backward` are inverse homotopy
/// equivalences.
#[derive(Clone, Debug)]
pub struct MinimalReduction {
    pub(super) minimal: ProjectiveComplex,
    pub(super) forward: ChainMap,
    pub(super) backward: ChainMap,
}

impl MinimalReduction {
    /// Reduces `complex` by Gaussian elimination and trims zero end terms.
    ///
    /// A complex without an isomorphism component keeps its term data and
    /// only loses zero end terms. Returns `None` when the complex is
    /// contractible.
    pub(super) fn new(
        complex: &ProjectiveComplex,
        meter: &mut WorkMeter,
    ) -> Result<Option<MinimalReduction>, Interrupt> {
        let mut state = Elimination::new(complex, meter)?;
        if state.pivot().is_none() {
            return Self::trimmed(complex.complex());
        }
        while let Some((offset, row, column)) = state.pivot() {
            meter.charge()?;
            state.eliminate(offset, row, column)?;
        }
        Self::assembled(complex, &state)
    }

    fn assembled(
        complex: &ProjectiveComplex,
        state: &Elimination,
    ) -> Result<Option<MinimalReduction>, Interrupt> {
        let assembled = assemble_elimination(complex, state)?;
        let Some(support) = support(&assembled.sums) else {
            return Ok(None);
        };
        let source = complex.complex();
        let minimal = restricted(
            source.lower(),
            &assembled.sums,
            &assembled.differentials,
            support,
        )?;
        let forward = ChainMap::new(source, &minimal, assembled.forward)?;
        let backward = ChainMap::new(&minimal, source, assembled.backward)?;
        Ok(Some(MinimalReduction {
            minimal: ProjectiveComplex::new(minimal)?,
            forward,
            backward,
        }))
    }

    fn trimmed(source: &BoundedComplex) -> Result<Option<MinimalReduction>, Interrupt> {
        let Some(support) = support(source.terms()) else {
            return Ok(None);
        };
        let minimal = restricted(
            source.lower(),
            source.terms(),
            source.differentials(),
            support,
        )?;
        let zero = Module::zero(source.terms()[0].algebra());
        let kept = |offset: usize| (support.0..=support.1).contains(&offset);
        let components = |into_term: bool| {
            source
                .terms()
                .iter()
                .enumerate()
                .map(|(offset, term)| match (kept(offset), into_term) {
                    (true, _) => Ok(identity(term)),
                    (false, true) => zero_morphism(&zero, term),
                    (false, false) => zero_morphism(term, &zero),
                })
                .collect::<Result<Vec<_>, HomError>>()
        };
        let forward = ChainMap::new(source, &minimal, components(false)?)?;
        let backward = ChainMap::new(&minimal, source, components(true)?)?;
        Ok(Some(MinimalReduction {
            minimal: ProjectiveComplex::new(minimal)?,
            forward,
            backward,
        }))
    }

    accessor_methods! {
        /// The minimal projective complex.
        pub minimal() -> &ProjectiveComplex = |this| &this.minimal;
        /// The chain map from the source to the minimal complex.
        pub forward() -> &ChainMap = |this| &this.forward;
        /// The chain map from the minimal complex to the source.
        pub backward() -> &ChainMap = |this| &this.backward;
    }

    /// Rechecks both chain maps, the identity composite, the homology
    /// dimensions, minimality, and nonzero end terms against `source`.
    pub fn verify(&self, source: &BoundedComplex) -> bool {
        let minimal = self.minimal.complex();
        let composite = self.backward.then(&self.forward);
        self.minimal.verify()
            && support(minimal.terms()) == Some((0, minimal.len() - 1))
            && self.forward.verify()
            && self.backward.verify()
            && self.forward.source().agrees_with(source)
            && self.backward.target().agrees_with(source)
            && minimal.padded_to(source.range()).is_ok_and(|padded| {
                padded.agrees_with(self.forward.target())
                    && padded.agrees_with(self.backward.source())
            })
            && composite
                .is_ok_and(|map| map.agrees_with(&ChainMap::identity(self.backward.source())))
            && homology(source)
                .is_some_and(|homology_source| Some(homology_source) == homology(minimal))
            && is_minimal(&self.minimal)
    }
}

/// Whether no differential component of `complex` is an isomorphism.
pub(super) fn is_minimal(complex: &ProjectiveComplex) -> bool {
    Elimination::new(complex, &mut WorkMeter::default()).is_ok_and(|state| state.pivot().is_none())
}
