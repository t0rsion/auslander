//! Strict bounded transport for a split tilting target.
//!
//! The transport applies `Hom_A(T, -)` to terms with an [`AddClosureWitness`].
//! Its inverse applies the checked target isomorphism to a stored projective
//! decomposition. It does not resolve arbitrary modules.

use std::sync::Arc;

use crate::algebra::Algebra;
use crate::basic::{AddClosureWitness, BasicDecomposition};
use crate::decompose::{
    Split, SplitError, add_morphisms, direct_sum_or_zero, inverse_morphism, mutually_inverse,
};
use crate::hom::{HomError, Morphism, identity, zero_morphism};
use crate::homotopy::{
    BoundedComplex, BoundedComplexError, ChainHomQuotient, ChainHomSpace, ChainHomotopy, ChainMap,
    ChainMapError, DegreeRange,
};
use crate::homspace::{HomSpace, HomSpaceError, row_times};
use crate::iso::{IsoOutcome, is_isomorphic};
use crate::linalg::DenseMat;
use crate::module::{Module, ModuleError, same_representation, summand_sum};
use crate::resolution::{ProjectiveResolution, ResolutionEnd, resolve};
use crate::target::VerifiedTargetPresentation;
use crate::tilting::ClassicalTiltingModule;

/// Rejected strict transport input or a failed checked construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TransportError {
    /// The supplied target presentation does not verify.
    InvalidTarget,
    /// A source term has no witness.
    SourceWitnessCount { expected: usize, got: usize },
    /// The source witness at `term` does not verify.
    InvalidSourceWitness { term: usize },
    /// The source witness at `term` belongs to another tilting module.
    SourceWitnessTarget { term: usize },
    /// The source witness at `term` belongs to another complex term.
    SourceWitnessTerm { term: usize },
    /// The target term at `term` is not projective.
    TargetTermNotProjective { term: usize },
    /// A stored target summand does not match one canonical projective.
    TargetSummandMatch { term: usize, summand: usize },
    /// A stored source summand does not match one target summand.
    SourceSummandMatch { term: usize, summand: usize },
    /// A required isomorphism was not certified.
    Isomorphism { reason: String },
    /// A split did not pass its defining identities.
    Split(SplitError),
    /// A module action or morphism failed its checked constructor.
    Module(ModuleError),
    /// A module morphism failed its checked constructor or composition.
    Hom(HomError),
    /// Coordinates did not belong to their deterministic Hom space.
    HomSpace(HomSpaceError),
    /// A bounded complex failed its checked constructor.
    Complex(BoundedComplexError),
    /// A chain map failed its checked constructor.
    Chain(ChainMapError),
    /// A chain map is not stored on the supplied source and target complexes.
    ChainDomain,
    /// A homotopy is not stored on the supplied source and target complexes.
    HomotopyDomain,
    /// A stored construction violated an internal invariant.
    Defect { reason: String },
}

display_error! { TransportError {
    Self::InvalidTarget => "target presentation does not verify";
    Self::SourceWitnessCount { expected, got } => "source complex has {got} witnesses, expected {expected}";
    Self::InvalidSourceWitness { term } => "source witness at term {term} does not verify";
    Self::SourceWitnessTarget { term } => "source witness at term {term} belongs to another tilting module";
    Self::SourceWitnessTerm { term } => "source witness at term {term} belongs to another complex term";
    Self::TargetTermNotProjective { term } => "target term {term} has no verified canonical-projective decomposition";
    Self::TargetSummandMatch { term, summand } => "target term {term} summand {summand} matches no canonical projective";
    Self::SourceSummandMatch { term, summand } => "source term {term} summand {summand} matches no target summand";
    Self::Isomorphism { reason } => "isomorphism was not certified: {reason}";
    Self::Split(error) => "split rejected: {error}";
    Self::Module(error) => "module rejected: {error}";
    Self::Hom(error) => "morphism rejected: {error}";
    Self::HomSpace(error) => "Hom-space coordinates rejected: {error}";
    Self::Complex(error) => "complex rejected: {error}";
    Self::Chain(error) => "chain map rejected: {error}";
    Self::ChainDomain => "chain map does not use the supplied source and target complexes";
    Self::HomotopyDomain => "homotopy does not use the supplied source and target complexes";
    Self::Defect { reason } => "internal transport check failed: {reason}";
} }

error_source! { TransportError {
    Self::Split(error) => Some(error),
    Self::Module(error) => Some(error),
    Self::Hom(error) => Some(error),
    Self::HomSpace(error) => Some(error),
    Self::Complex(error) => Some(error),
    Self::Chain(error) => Some(error),
    _ => None,
} }

from_variants! { TransportError {
    SplitError => Split,
    ModuleError => Module,
    HomError => Hom,
    HomSpaceError => HomSpace,
    BoundedComplexError => Complex,
    ChainMapError => Chain,
} }

/// A bounded complex whose terms carry verified membership in `add(T)`.
#[derive(Clone, Debug)]
pub struct AddTComplex {
    complex: BoundedComplex,
    witnesses: Vec<AddClosureWitness>,
}

impl AddTComplex {
    /// Builds a bounded `add(T)` complex from one witness per term.
    pub fn new(
        complex: BoundedComplex,
        witnesses: Vec<AddClosureWitness>,
    ) -> Result<AddTComplex, TransportError> {
        if witnesses.len() != complex.len() {
            return Err(TransportError::SourceWitnessCount {
                expected: complex.len(),
                got: witnesses.len(),
            });
        }
        for (term, (module, witness)) in complex.terms().iter().zip(&witnesses).enumerate() {
            if !witness.verify() {
                return Err(TransportError::InvalidSourceWitness { term });
            }
            if !witness.module().ptr_eq(module) {
                return Err(TransportError::SourceWitnessTerm { term });
            }
        }
        Ok(AddTComplex { complex, witnesses })
    }

    accessor_methods! {
        /// The bounded source complex.
        pub complex() -> &BoundedComplex = |this| &this.complex;
        /// One verified `add(T)` witness per source term.
        pub witnesses() -> &[AddClosureWitness] = |this| &this.witnesses;
    }

    /// Rechecks the complex and every stored term witness.
    pub fn verify(&self) -> bool {
        self.complex.verify()
            && self.witnesses.len() == self.complex.len()
            && self
                .complex
                .terms()
                .iter()
                .zip(&self.witnesses)
                .all(|(term, witness)| witness.verify() && witness.module().ptr_eq(term))
    }
}

#[derive(Clone, Debug)]
struct SourceTerm {
    module: Module,
    split: Split,
    indices: Vec<usize>,
    to_target: Vec<Morphism>,
    from_target: Vec<Morphism>,
}

impl SourceTerm {
    fn verify(&self, target_summands: &[Module]) -> bool {
        self.split.verify()
            && self.split.total().ptr_eq(&self.module)
            && self.indices.len() == self.split.summands().len()
            && self.to_target.len() == self.indices.len()
            && self.from_target.len() == self.indices.len()
            && self.indices.iter().enumerate().all(|(slot, &index)| {
                target_summands.get(index).is_some_and(|target| {
                    self.to_target[slot]
                        .source()
                        .ptr_eq(&self.split.summands()[slot])
                        && self.to_target[slot].target().ptr_eq(target)
                        && self.from_target[slot].source().ptr_eq(target)
                        && self.from_target[slot]
                            .target()
                            .ptr_eq(&self.split.summands()[slot])
                        && mutually_inverse(&self.to_target[slot], &self.from_target[slot])
                })
            })
    }
}

#[derive(Clone, Debug)]
struct ProjectiveTerm {
    module: Module,
    split: Split,
    indices: Vec<usize>,
    to_canonical: Vec<Morphism>,
    from_canonical: Vec<Morphism>,
    source: SourceTerm,
}

impl ProjectiveTerm {
    fn verify(&self, target_summands: &[Module], canonical_projectives: &[Module]) -> bool {
        self.split.verify()
            && self.split.total().ptr_eq(&self.module)
            && self.indices.len() == self.split.summands().len()
            && self.to_canonical.len() == self.indices.len()
            && self.from_canonical.len() == self.indices.len()
            && self.source.verify(target_summands)
            && self.source.indices == self.indices
            && self.indices.iter().enumerate().all(|(slot, &index)| {
                canonical_projectives.get(index).is_some_and(|projective| {
                    self.to_canonical[slot]
                        .source()
                        .ptr_eq(&self.split.summands()[slot])
                        && self.to_canonical[slot].target().ptr_eq(projective)
                        && self.from_canonical[slot].source().ptr_eq(projective)
                        && self.from_canonical[slot]
                            .target()
                            .ptr_eq(&self.split.summands()[slot])
                        && mutually_inverse(&self.to_canonical[slot], &self.from_canonical[slot])
                })
            })
    }
}

/// A bounded target complex with a canonical-projective decomposition per term.
#[derive(Clone, Debug)]
pub struct ProjectiveTargetComplex {
    complex: BoundedComplex,
    terms: Vec<ProjectiveTerm>,
    target_summands: Vec<Module>,
    canonical_projectives: Vec<Module>,
}

impl ProjectiveTargetComplex {
    accessor_methods! {
        /// The bounded complex over the recovered target algebra.
        pub complex() -> &BoundedComplex = |this| &this.complex;
    }

    /// Rechecks every stored target term decomposition and the bounded complex.
    pub fn verify(&self) -> bool {
        self.complex.verify()
            && self.terms.len() == self.complex.len()
            && self
                .complex
                .terms()
                .iter()
                .zip(&self.terms)
                .all(|(term, model)| {
                    term.ptr_eq(&model.module)
                        && model.verify(&self.target_summands, &self.canonical_projectives)
                })
    }
}

/// Two mutually inverse checked chain maps.
#[derive(Clone, Debug)]
pub struct ChainIsomorphism {
    forward: ChainMap,
    backward: ChainMap,
}

impl ChainIsomorphism {
    /// Builds a chain isomorphism after checking both inverse identities.
    pub fn new(forward: ChainMap, backward: ChainMap) -> Result<ChainIsomorphism, TransportError> {
        let round = forward.then(&backward)?;
        let back = backward.then(&forward)?;
        if !round.agrees_with(&ChainMap::identity(forward.source()))
            || !back.agrees_with(&ChainMap::identity(forward.target()))
        {
            return Err(TransportError::Defect {
                reason: "stored chain maps are not mutual inverses".to_string(),
            });
        }
        Ok(ChainIsomorphism { forward, backward })
    }

    accessor_methods! {
        /// The forward chain map.
        pub forward() -> &ChainMap = |this| &this.forward;
        /// The inverse chain map.
        pub backward() -> &ChainMap = |this| &this.backward;
    }

    /// Rechecks both chain maps and both inverse identities.
    pub fn verify(&self) -> bool {
        self.forward.verify()
            && self.backward.verify()
            && ChainIsomorphism::new(self.forward.clone(), self.backward.clone()).is_ok()
    }
}

/// The strict additive transport fixed by one verified target presentation.
#[derive(Clone)]
pub struct StrictTransport {
    target: VerifiedTargetPresentation,
    source_basic: BasicDecomposition,
    target_basic: BasicDecomposition,
    canonical_projectives: Vec<Module>,
}

debug_fields!(StrictTransport |this| {
    "source_dim_vector" => this.target.source().dim_vector();
    "target_dim" => this.target.target().dim();
});

fn direct_sum_split(algebra: &Arc<Algebra>, parts: &[Module]) -> Result<Split, TransportError> {
    let (total, inclusions, projections) = direct_sum_or_zero(algebra, parts.iter());
    Ok(Split::new(&total, parts.to_vec(), inclusions, projections)?)
}

fn compose_three(
    first: &Morphism,
    second: &Morphism,
    third: &Morphism,
) -> Result<Morphism, TransportError> {
    Ok(first.then(second)?.then(third)?)
}

fn sum_terms(
    source: &Module,
    target: &Module,
    terms: impl IntoIterator<Item = Morphism>,
) -> Result<Morphism, TransportError> {
    let mut sum = zero_morphism(source, target)?;
    for term in terms {
        sum = add_morphisms(&sum, &term);
    }
    Ok(sum)
}

fn rebase_morphism(
    map: &Morphism,
    source: &Module,
    target: &Module,
) -> Result<Morphism, TransportError> {
    if !same_representation(map.source(), source) || !same_representation(map.target(), target) {
        return Err(TransportError::Defect {
            reason: "morphism endpoints do not match their checked representations".to_string(),
        });
    }
    let matrices = (0..source.algebra().quiver().num_vertices())
        .map(|vertex| map.map_at(vertex).clone())
        .collect();
    Morphism::new(source, target, matrices).map_err(Into::into)
}

fn agrees_after_padding(left: &BoundedComplex, right: &BoundedComplex) -> bool {
    let Ok(range) = DegreeRange::new(
        left.lower().min(right.lower()),
        left.upper().max(right.upper()),
    ) else {
        return false;
    };
    left.padded_to(range).is_ok_and(|left| {
        right
            .padded_to(range)
            .is_ok_and(|right| left.agrees_with(&right))
    })
}

fn transported_components(
    range: DegreeRange,
    source: (&BoundedComplex, &BoundedComplex),
    target: (&BoundedComplex, &BoundedComplex),
    family: (&[Morphism], usize),
    mut transport: impl FnMut(usize, usize, &Morphism) -> Result<Morphism, TransportError>,
) -> Result<Vec<Morphism>, TransportError> {
    let (components, target_offset) = family;
    let source_padded = source.1.padded_to(range)?;
    let target_padded = target.1.padded_to(range)?;
    (0..range.len().saturating_sub(target_offset))
        .map(|index| {
            let degree = (i64::from(range.lower()) + index as i64) as i32;
            let target_degree = degree
                .checked_add(target_offset as i32)
                .expect("the component range excludes target degree overflow");
            if source.0.range().contains(degree) && target.0.range().contains(target_degree) {
                transport(
                    (i64::from(degree) - i64::from(source.0.lower())) as usize,
                    (i64::from(target_degree) - i64::from(target.0.lower())) as usize,
                    &components[index],
                )
            } else {
                zero_morphism(
                    &source_padded.terms()[index],
                    &target_padded.terms()[index + target_offset],
                )
                .map_err(Into::into)
            }
        })
        .collect()
}

impl StrictTransport {
    /// Builds strict transport from one verified split target presentation.
    pub fn new(target: VerifiedTargetPresentation) -> Result<StrictTransport, TransportError> {
        if !target.verify() {
            return Err(TransportError::InvalidTarget);
        }
        let source_basic = BasicDecomposition::new(target.source()).map_err(|error| {
            TransportError::Isomorphism {
                reason: format!("source basic decomposition failed: {error}"),
            }
        })?;
        let canonical_projectives: Vec<Module> = (0..target.target().quiver().num_vertices())
            .map(|vertex| Module::projective(target.target(), vertex))
            .collect();
        let regular = summand_sum(
            target.target(),
            &(0..target.target().quiver().num_vertices()).collect::<Vec<_>>(),
            Module::projective,
        );
        let target_basic =
            BasicDecomposition::new(&regular).map_err(|error| TransportError::Isomorphism {
                reason: format!("target regular module is not certified basic: {error}"),
            })?;
        Ok(StrictTransport {
            target,
            source_basic,
            target_basic,
            canonical_projectives,
        })
    }

    accessor_methods! {
        /// The verified target presentation that fixes this transport.
        pub target() -> &VerifiedTargetPresentation = |this| &this.target;
    }

    /// Rechecks the target and every fixed canonical summand model.
    pub fn verify(&self) -> bool {
        self.target.verify()
            && self.source_basic.module().ptr_eq(self.target.source())
            && Arc::ptr_eq(self.target_basic.module().algebra(), self.target.target())
            && self.canonical_projectives.len()
                == self.target.target().quiver().num_vertices() as usize
            && self
                .canonical_projectives
                .iter()
                .enumerate()
                .all(|(vertex, projective)| {
                    same_representation(
                        projective,
                        &Module::projective(self.target.target(), vertex as u32),
                    )
                })
    }

    fn target_summands(&self) -> &[Module] {
        self.target.split().summands()
    }

    fn source_term(
        &self,
        witness: &AddClosureWitness,
        term: usize,
    ) -> Result<SourceTerm, TransportError> {
        if !witness.verify() {
            return Err(TransportError::InvalidSourceWitness { term });
        }
        if !witness.target().ptr_eq(self.target.source()) {
            return Err(TransportError::SourceWitnessTarget { term });
        }
        let mut indices = Vec::with_capacity(witness.summands().len());
        let mut to_target = Vec::with_capacity(witness.summands().len());
        let mut from_target = Vec::with_capacity(witness.summands().len());
        for (summand, matched) in witness.matches().iter().enumerate() {
            let matched_target = witness
                .target_summands()
                .get(matched.target_index())
                .ok_or(TransportError::SourceSummandMatch { term, summand })?;
            let Some((index, target_iso)) = self
                .target_summands()
                .iter()
                .enumerate()
                .find_map(|(index, target_summand)| {
                    match is_isomorphic(matched_target, target_summand) {
                        Ok(IsoOutcome::Isomorphic(map)) => Some(Ok((index, map))),
                        Ok(IsoOutcome::NotIsomorphic(_) | IsoOutcome::Unknown { .. }) => None,
                        Err(error) => Some(Err(error)),
                    }
                })
                .transpose()?
            else {
                return Err(TransportError::SourceSummandMatch { term, summand });
            };
            let forward = matched.forward().then(&target_iso)?;
            let backward =
                inverse_morphism(&forward).ok_or_else(|| TransportError::Isomorphism {
                    reason: format!("source term {term} summand {summand} has no inverse"),
                })?;
            indices.push(index);
            to_target.push(forward);
            from_target.push(backward);
        }
        Ok(SourceTerm {
            module: witness.module().clone(),
            split: witness.split().clone(),
            indices,
            to_target,
            from_target,
        })
    }

    fn canonical_source_term(&self, indices: &[usize]) -> Result<SourceTerm, TransportError> {
        let parts: Vec<Module> = indices
            .iter()
            .map(|&index| self.target_summands()[index].clone())
            .collect();
        let split = direct_sum_split(self.target.source().algebra(), &parts)?;
        let to_target = parts.iter().map(identity).collect();
        let from_target = parts.iter().map(identity).collect();
        Ok(SourceTerm {
            module: split.total().clone(),
            split,
            indices: indices.to_vec(),
            to_target,
            from_target,
        })
    }

    fn forward_module(&self, module: &Module) -> Result<(Module, Vec<HomSpace>), TransportError> {
        let homs: Vec<HomSpace> = self
            .target_summands()
            .iter()
            .map(|summand| HomSpace::new(summand, module).map_err(TransportError::Hom))
            .collect::<Result<_, _>>()?;
        let dims = homs.iter().map(HomSpace::dim).collect();
        let quiver = self.target.target().quiver();
        let maps: Vec<DenseMat> = (0..quiver.num_arrows())
            .map(|arrow| {
                let arrow_id = crate::quiver::ArrowId(arrow as u32);
                let source = quiver.source(arrow_id) as usize;
                let destination = quiver.target(arrow_id) as usize;
                let image = self
                    .target
                    .endo()
                    .morphism(self.target.arrow_images().row(arrow));
                let precompose = compose_three(
                    &self.target.split().inclusions()[destination],
                    &image,
                    &self.target.split().projections()[source],
                )?;
                let mut matrix = DenseMat::zero(homs[source].dim(), homs[destination].dim());
                for row in 0..homs[source].dim() {
                    let composite = precompose.then(&homs[source].basis_morphism(row))?;
                    let coordinates = homs[destination].coords(&composite)?;
                    for (column, value) in coordinates.into_iter().enumerate() {
                        matrix.set(row, column, value);
                    }
                }
                Ok(matrix)
            })
            .collect::<Result<_, TransportError>>()?;
        Ok((Module::new(self.target.target().clone(), dims, maps)?, homs))
    }

    fn forward_morphism(
        &self,
        source_image: &Module,
        source_homs: &[HomSpace],
        target_image: &Module,
        target_homs: &[HomSpace],
        map: &Morphism,
    ) -> Result<Morphism, TransportError> {
        let Some(source_term) = source_homs.first().map(HomSpace::target) else {
            return Err(TransportError::Defect {
                reason: "the target presentation has no vertices".to_string(),
            });
        };
        let Some(target_term) = target_homs.first().map(HomSpace::target) else {
            return Err(TransportError::Defect {
                reason: "the target presentation has no vertices".to_string(),
            });
        };
        if !map.source().ptr_eq(source_term) || !map.target().ptr_eq(target_term) {
            return Err(TransportError::Defect {
                reason: "forward morphism endpoints do not match their term models".to_string(),
            });
        }
        let matrices: Vec<DenseMat> = source_homs
            .iter()
            .zip(target_homs)
            .map(|(source, target)| {
                let mut matrix = DenseMat::zero(source.dim(), target.dim());
                for row in 0..source.dim() {
                    let composite = source.basis_morphism(row).then(map)?;
                    let coordinates = target.coords(&composite)?;
                    for (column, value) in coordinates.into_iter().enumerate() {
                        matrix.set(row, column, value);
                    }
                }
                Ok(matrix)
            })
            .collect::<Result<_, TransportError>>()?;
        Ok(Morphism::new(source_image, target_image, matrices)?)
    }

    fn canonical_forward_iso(
        &self,
        index: usize,
        image: &Module,
        homs: &[HomSpace],
    ) -> Result<(Morphism, Morphism), TransportError> {
        let projective = &self.canonical_projectives[index];
        let algebra = self.target.target();
        let matrices: Vec<DenseMat> = (0..algebra.quiver().num_vertices())
            .map(|vertex| {
                let space = &homs[vertex as usize];
                let mut matrix = DenseMat::zero(space.dim(), projective.dim_at(vertex));
                let path_indices = algebra.paths_between(index as u32, vertex);
                for row in 0..space.dim() {
                    let map = space.basis_morphism(row);
                    let extension = compose_three(
                        &self.target.split().projections()[vertex as usize],
                        &map,
                        &self.target.split().inclusions()[index],
                    )?;
                    let coordinates = self
                        .target
                        .preimage_coordinates(&self.target.endo().coords(&extension));
                    for (column, &basis) in path_indices.iter().enumerate() {
                        matrix.set(row, column, coordinates[basis]);
                    }
                }
                Ok(matrix)
            })
            .collect::<Result<_, TransportError>>()?;
        let forward = Morphism::new(image, projective, matrices)?;
        let backward = inverse_morphism(&forward).ok_or_else(|| TransportError::Isomorphism {
            reason: format!("Hom(T, T_{index}) did not map invertibly to e_{index}B"),
        })?;
        Ok((forward, backward))
    }

    fn forward_term(&self, source: &SourceTerm) -> Result<ForwardTerm, TransportError> {
        let (module, homs) = self.forward_module(&source.module)?;
        let mut projectives = Vec::with_capacity(source.indices.len());
        let mut inclusions = Vec::with_capacity(source.indices.len());
        let mut projections = Vec::with_capacity(source.indices.len());
        for (slot, &index) in source.indices.iter().enumerate() {
            let summand = &source.split.summands()[slot];
            let (summand_image, summand_homs) = self.forward_module(summand)?;
            let forward_projection = self.forward_morphism(
                &module,
                &homs,
                &summand_image,
                &summand_homs,
                &source.split.projections()[slot],
            )?;
            let forward_inclusion = self.forward_morphism(
                &summand_image,
                &summand_homs,
                &module,
                &homs,
                &source.split.inclusions()[slot],
            )?;
            let (target_image, target_homs) =
                self.forward_module(&self.target_summands()[index])?;
            let forward_to_target = self.forward_morphism(
                &summand_image,
                &summand_homs,
                &target_image,
                &target_homs,
                &source.to_target[slot],
            )?;
            let forward_from_target = self.forward_morphism(
                &target_image,
                &target_homs,
                &summand_image,
                &summand_homs,
                &source.from_target[slot],
            )?;
            let (target_to_projective, target_from_projective) =
                self.canonical_forward_iso(index, &target_image, &target_homs)?;
            let projection = compose_three(
                &forward_projection,
                &forward_to_target,
                &target_to_projective,
            )?;
            let inclusion = compose_three(
                &target_from_projective,
                &forward_from_target,
                &forward_inclusion,
            )?;
            projectives.push(self.canonical_projectives[index].clone());
            projections.push(projection);
            inclusions.push(inclusion);
        }
        let split = Split::new(&module, projectives, inclusions, projections)?;
        let source_image = self.canonical_source_term(&source.indices)?;
        let unit = sum_terms(
            &source.module,
            &source_image.module,
            source.indices.iter().enumerate().map(|(slot, _)| {
                compose_three(
                    &source.split.projections()[slot],
                    &source.to_target[slot],
                    &source_image.split.inclusions()[slot],
                )
                .expect("source split endpoints agree")
            }),
        )?;
        let unit_inverse = inverse_morphism(&unit).ok_or_else(|| TransportError::Isomorphism {
            reason: "source term did not map invertibly to its canonical target sum".to_string(),
        })?;
        let indices = source.indices.clone();
        let count = indices.len();
        let projective = ProjectiveTerm {
            module: module.clone(),
            split,
            indices: indices.clone(),
            to_canonical: (0..count)
                .map(|slot| identity(&self.canonical_projectives[indices[slot]]))
                .collect(),
            from_canonical: (0..count)
                .map(|slot| identity(&self.canonical_projectives[indices[slot]]))
                .collect(),
            source: source_image,
        };
        Ok(ForwardTerm {
            module,
            homs,
            projective,
            unit,
            unit_inverse,
        })
    }

    fn projective_term(
        &self,
        module: &Module,
        term: usize,
    ) -> Result<ProjectiveTerm, TransportError> {
        let Some(witness) =
            AddClosureWitness::from_module(module, &self.target_basic).map_err(|error| {
                TransportError::Isomorphism {
                    reason: format!("target term {term} decomposition failed: {error}"),
                }
            })?
        else {
            return Err(TransportError::TargetTermNotProjective { term });
        };
        let mut indices = Vec::with_capacity(witness.summands().len());
        let mut to_canonical = Vec::with_capacity(witness.summands().len());
        let mut from_canonical = Vec::with_capacity(witness.summands().len());
        for (summand, matched) in witness.matches().iter().enumerate() {
            let basic_summand = self
                .target_basic
                .summands()
                .get(matched.target_index())
                .ok_or(TransportError::TargetSummandMatch { term, summand })?;
            let Some((index, basic_to_canonical)) = self
                .canonical_projectives
                .iter()
                .enumerate()
                .find_map(|(index, projective)| {
                    crate::iso::indecomposable_iso(
                        basic_summand.module(),
                        projective,
                        basic_summand.endo(),
                    )
                    .map(|map| (index, map))
                })
            else {
                return Err(TransportError::TargetSummandMatch { term, summand });
            };
            let forward = matched.forward().then(&basic_to_canonical)?;
            let backward =
                inverse_morphism(&forward).ok_or_else(|| TransportError::Isomorphism {
                    reason: format!("target term {term} summand {summand} has no inverse"),
                })?;
            indices.push(index);
            to_canonical.push(forward);
            from_canonical.push(backward);
        }
        let source = self.canonical_source_term(&indices)?;
        Ok(ProjectiveTerm {
            module: module.clone(),
            split: witness.split().clone(),
            indices,
            to_canonical,
            from_canonical,
            source,
        })
    }

    fn target_block_to_source(
        &self,
        block: &Morphism,
        source: usize,
        target: usize,
    ) -> Result<Morphism, TransportError> {
        let algebra = self.target.target();
        let trivial = algebra
            .paths_between(source as u32, source as u32)
            .iter()
            .position(|&basis| algebra.basis()[basis].is_trivial())
            .ok_or_else(|| TransportError::Defect {
                reason: format!("target vertex {source} has no trivial path"),
            })?;
        let element = block.map_at(source as u32).row(trivial).to_vec();
        let mut coordinates = vec![algebra.field().zero(); algebra.dim()];
        for (slot, &basis) in algebra
            .paths_between(target as u32, source as u32)
            .iter()
            .enumerate()
        {
            coordinates[basis] = element[slot];
        }
        let endomorphism = self
            .target
            .endo()
            .morphism(&self.target.map_coordinates(&coordinates));
        compose_three(
            &self.target.split().inclusions()[source],
            &endomorphism,
            &self.target.split().projections()[target],
        )
    }

    fn reverse_morphism(
        &self,
        source: &ProjectiveTerm,
        target: &ProjectiveTerm,
        map: &Morphism,
    ) -> Result<Morphism, TransportError> {
        let map = if map.source().ptr_eq(&source.module) && map.target().ptr_eq(&target.module) {
            map.clone()
        } else {
            rebase_morphism(map, &source.module, &target.module)?
        };
        let mut terms = Vec::new();
        for (left, &source_index) in source.indices.iter().enumerate() {
            for (right, &target_index) in target.indices.iter().enumerate() {
                let block = compose_three(
                    &source.from_canonical[left],
                    &source.split.inclusions()[left],
                    &map,
                )?
                .then(&target.split.projections()[right])?
                .then(&target.to_canonical[right])?;
                let source_block =
                    self.target_block_to_source(&block, source_index, target_index)?;
                terms.push(compose_three(
                    &source.source.split.projections()[left],
                    &source_block,
                    &target.source.split.inclusions()[right],
                )?);
            }
        }
        sum_terms(&source.source.module, &target.source.module, terms)
    }

    fn forward_terms(&self, source: &AddTComplex) -> Result<Vec<ForwardTerm>, TransportError> {
        if !source.verify() {
            return Err(TransportError::Defect {
                reason: "source add(T) complex does not verify".to_string(),
            });
        }
        let source_terms: Vec<SourceTerm> = source
            .witnesses()
            .iter()
            .enumerate()
            .map(|(term, witness)| self.source_term(witness, term))
            .collect::<Result<_, _>>()?;
        source_terms
            .iter()
            .map(|term| self.forward_term(term))
            .collect()
    }

    fn forward_complex_from_terms(
        &self,
        source: &BoundedComplex,
        terms: &[ForwardTerm],
    ) -> Result<ProjectiveTargetComplex, TransportError> {
        let maps: Vec<Morphism> = source
            .differentials()
            .iter()
            .enumerate()
            .map(|(index, map)| {
                self.forward_morphism(
                    &terms[index + 1].module,
                    &terms[index + 1].homs,
                    &terms[index].module,
                    &terms[index].homs,
                    map,
                )
            })
            .collect::<Result<_, _>>()?;
        let complex = BoundedComplex::new(
            source.lower(),
            terms.iter().map(|term| term.module.clone()).collect(),
            maps,
        )?;
        Ok(ProjectiveTargetComplex {
            complex,
            terms: terms.iter().map(|term| term.projective.clone()).collect(),
            target_summands: self.target_summands().to_vec(),
            canonical_projectives: self.canonical_projectives.clone(),
        })
    }

    /// Verifies projectivity of every target term and stores its decomposition.
    pub fn target_complex(
        &self,
        complex: BoundedComplex,
    ) -> Result<ProjectiveTargetComplex, TransportError> {
        let terms: Vec<ProjectiveTerm> = complex
            .terms()
            .iter()
            .enumerate()
            .map(|(term, module)| self.projective_term(module, term))
            .collect::<Result<_, _>>()?;
        Ok(ProjectiveTargetComplex {
            complex,
            terms,
            target_summands: self.target_summands().to_vec(),
            canonical_projectives: self.canonical_projectives.clone(),
        })
    }

    /// Transports a bounded `add(T)` complex to target projectives.
    pub fn forward(&self, source: &AddTComplex) -> Result<ProjectiveTargetComplex, TransportError> {
        let terms = self.forward_terms(source)?;
        self.forward_complex_from_terms(source.complex(), &terms)
    }

    /// Transports a checked chain map between bounded `add(T)` complexes.
    pub fn forward_chain_map(
        &self,
        source: &AddTComplex,
        target: &AddTComplex,
        map: &ChainMap,
    ) -> Result<ChainMap, TransportError> {
        if !agrees_after_padding(map.source(), source.complex())
            || !agrees_after_padding(map.target(), target.complex())
        {
            return Err(TransportError::ChainDomain);
        }
        let source_terms = self.forward_terms(source)?;
        let target_terms = self.forward_terms(target)?;
        let source_image = self.forward_complex_from_terms(source.complex(), &source_terms)?;
        let target_image = self.forward_complex_from_terms(target.complex(), &target_terms)?;
        let components = transported_components(
            map.range(),
            (source.complex(), source_image.complex()),
            (target.complex(), target_image.complex()),
            (map.components(), 0),
            |source_index, target_index, component| {
                self.forward_morphism(
                    &source_terms[source_index].module,
                    &source_terms[source_index].homs,
                    &target_terms[target_index].module,
                    &target_terms[target_index].homs,
                    component,
                )
            },
        )?;
        ChainMap::new(source_image.complex(), target_image.complex(), components)
            .map_err(Into::into)
    }

    /// Transports a chain homotopy between bounded `add(T)` complexes.
    pub fn forward_homotopy(
        &self,
        source: &AddTComplex,
        target: &AddTComplex,
        homotopy: &ChainHomotopy,
    ) -> Result<ChainHomotopy, TransportError> {
        if !agrees_after_padding(homotopy.source(), source.complex())
            || !agrees_after_padding(homotopy.target(), target.complex())
        {
            return Err(TransportError::HomotopyDomain);
        }
        let source_terms = self.forward_terms(source)?;
        let target_terms = self.forward_terms(target)?;
        let source_image = self.forward_complex_from_terms(source.complex(), &source_terms)?;
        let target_image = self.forward_complex_from_terms(target.complex(), &target_terms)?;
        let range = DegreeRange::new(
            homotopy.source().lower().min(homotopy.target().lower()),
            homotopy.source().upper().max(homotopy.target().upper()),
        )
        .map_err(|error| TransportError::Defect {
            reason: format!("homotopy support range failed: {error}"),
        })?;
        let components = transported_components(
            range,
            (source.complex(), source_image.complex()),
            (target.complex(), target_image.complex()),
            (homotopy.components(), 1),
            |source_index, target_index, component| {
                self.forward_morphism(
                    &source_terms[source_index].module,
                    &source_terms[source_index].homs,
                    &target_terms[target_index].module,
                    &target_terms[target_index].homs,
                    component,
                )
            },
        )?;
        ChainHomotopy::new(source_image.complex(), target_image.complex(), components)
            .map_err(Into::into)
    }

    /// Transports a mapping cone after transporting its chain map.
    pub fn forward_cone(
        &self,
        source: &AddTComplex,
        target: &AddTComplex,
        map: &ChainMap,
    ) -> Result<BoundedComplex, TransportError> {
        self.forward_chain_map(source, target, map)?
            .mapping_cone()
            .map_err(Into::into)
    }

    /// Transports an explicit homological shift of a bounded `add(T)` complex.
    pub fn forward_shift(
        &self,
        source: &AddTComplex,
        amount: i32,
    ) -> Result<ProjectiveTargetComplex, TransportError> {
        let shifted =
            AddTComplex::new(source.complex().shift(amount)?, source.witnesses().to_vec())?;
        self.forward(&shifted)
    }

    /// Transports the direct sum of bounded `add(T)` complexes.
    pub fn forward_direct_sum(
        &self,
        sources: &[&AddTComplex],
    ) -> Result<ProjectiveTargetComplex, TransportError> {
        let complexes: Vec<&BoundedComplex> =
            sources.iter().map(|source| source.complex()).collect();
        let complex = BoundedComplex::direct_sum(&complexes)?;
        let witnesses = complex
            .terms()
            .iter()
            .map(|term| {
                AddClosureWitness::from_module(term, &self.source_basic)
                    .map_err(|error| TransportError::Isomorphism {
                        reason: format!("direct-sum source term left add(T): {error}"),
                    })?
                    .ok_or_else(|| TransportError::Defect {
                        reason: "direct-sum source term left add(T)".to_string(),
                    })
            })
            .collect::<Result<_, _>>()?;
        self.forward(&AddTComplex::new(complex, witnesses)?)
    }

    /// Transports a bounded projective target complex back to `add(T)`.
    pub fn reverse(&self, target: &ProjectiveTargetComplex) -> Result<AddTComplex, TransportError> {
        if !target.verify() {
            return Err(TransportError::Defect {
                reason: "target projective complex does not verify".to_string(),
            });
        }
        let maps: Vec<Morphism> = target
            .complex
            .differentials()
            .iter()
            .enumerate()
            .map(|(index, map)| {
                self.reverse_morphism(&target.terms[index + 1], &target.terms[index], map)
            })
            .collect::<Result<_, _>>()?;
        let modules: Vec<Module> = target
            .terms
            .iter()
            .map(|term| term.source.module.clone())
            .collect();
        let witnesses = modules
            .iter()
            .map(|module| {
                AddClosureWitness::from_module(module, &self.source_basic)
                    .map_err(|error| TransportError::Isomorphism {
                        reason: format!("reverse target term left add(T): {error}"),
                    })?
                    .ok_or_else(|| TransportError::Defect {
                        reason: "a canonical target sum left add(T)".to_string(),
                    })
            })
            .collect::<Result<_, _>>()?;
        let complex = BoundedComplex::new(target.complex.lower(), modules, maps)?;
        AddTComplex::new(complex, witnesses)
    }

    /// Transports a checked chain map between bounded target projective complexes.
    pub fn reverse_chain_map(
        &self,
        source: &ProjectiveTargetComplex,
        target: &ProjectiveTargetComplex,
        map: &ChainMap,
    ) -> Result<ChainMap, TransportError> {
        if !agrees_after_padding(map.source(), source.complex())
            || !agrees_after_padding(map.target(), target.complex())
        {
            return Err(TransportError::ChainDomain);
        }
        let source_image = self.reverse(source)?;
        let target_image = self.reverse(target)?;
        let components = transported_components(
            map.range(),
            (source.complex(), source_image.complex()),
            (target.complex(), target_image.complex()),
            (map.components(), 0),
            |source_index, target_index, component| {
                self.reverse_morphism(
                    &source.terms[source_index],
                    &target.terms[target_index],
                    component,
                )
            },
        )?;
        ChainMap::new(source_image.complex(), target_image.complex(), components)
            .map_err(Into::into)
    }

    /// Transports a chain homotopy between bounded target projective complexes.
    pub fn reverse_homotopy(
        &self,
        source: &ProjectiveTargetComplex,
        target: &ProjectiveTargetComplex,
        homotopy: &ChainHomotopy,
    ) -> Result<ChainHomotopy, TransportError> {
        if !agrees_after_padding(homotopy.source(), source.complex())
            || !agrees_after_padding(homotopy.target(), target.complex())
        {
            return Err(TransportError::HomotopyDomain);
        }
        let source_image = self.reverse(source)?;
        let target_image = self.reverse(target)?;
        let range = DegreeRange::new(
            homotopy.source().lower().min(homotopy.target().lower()),
            homotopy.source().upper().max(homotopy.target().upper()),
        )
        .map_err(|error| TransportError::Defect {
            reason: format!("homotopy support range failed: {error}"),
        })?;
        let components = transported_components(
            range,
            (source.complex(), source_image.complex()),
            (target.complex(), target_image.complex()),
            (homotopy.components(), 1),
            |source_index, target_index, component| {
                self.reverse_morphism(
                    &source.terms[source_index],
                    &target.terms[target_index],
                    component,
                )
            },
        )?;
        ChainHomotopy::new(source_image.complex(), target_image.complex(), components)
            .map_err(Into::into)
    }

    /// Transports a target mapping cone after transporting its chain map.
    pub fn reverse_cone(
        &self,
        source: &ProjectiveTargetComplex,
        target: &ProjectiveTargetComplex,
        map: &ChainMap,
    ) -> Result<BoundedComplex, TransportError> {
        self.reverse_chain_map(source, target, map)?
            .mapping_cone()
            .map_err(Into::into)
    }

    /// Transports an explicit homological shift of a bounded target projective complex.
    pub fn reverse_shift(
        &self,
        target: &ProjectiveTargetComplex,
        amount: i32,
    ) -> Result<AddTComplex, TransportError> {
        let shifted = ProjectiveTargetComplex {
            complex: target.complex().shift(amount)?,
            terms: target.terms.clone(),
            target_summands: target.target_summands.clone(),
            canonical_projectives: target.canonical_projectives.clone(),
        };
        self.reverse(&shifted)
    }

    /// Transports the direct sum of bounded target projective complexes.
    pub fn reverse_direct_sum(
        &self,
        targets: &[&ProjectiveTargetComplex],
    ) -> Result<AddTComplex, TransportError> {
        let complexes: Vec<&BoundedComplex> =
            targets.iter().map(|target| target.complex()).collect();
        self.reverse(&self.target_complex(BoundedComplex::direct_sum(&complexes)?)?)
    }

    /// Returns the unit chain isomorphism for one bounded `add(T)` complex.
    pub fn source_round_trip(
        &self,
        source: &AddTComplex,
    ) -> Result<ChainIsomorphism, TransportError> {
        let forward_terms = self.forward_terms(source)?;
        let forward = self.forward_complex_from_terms(source.complex(), &forward_terms)?;
        let reverse = self.reverse(&forward)?;
        let unit = ChainMap::new(
            source.complex(),
            reverse.complex(),
            forward_terms.iter().map(|term| term.unit.clone()).collect(),
        )?;
        let inverse = ChainMap::new(
            reverse.complex(),
            source.complex(),
            forward_terms
                .iter()
                .map(|term| term.unit_inverse.clone())
                .collect(),
        )?;
        ChainIsomorphism::new(unit, inverse)
    }

    /// Returns the counit chain isomorphism for one bounded projective target complex.
    pub fn target_round_trip(
        &self,
        target: &ProjectiveTargetComplex,
    ) -> Result<ChainIsomorphism, TransportError> {
        let source = self.reverse(target)?;
        let forward_terms: Vec<ForwardTerm> = target
            .terms
            .iter()
            .map(|term| self.forward_term(&term.source))
            .collect::<Result<_, _>>()?;
        let forward = self.forward_complex_from_terms(source.complex(), &forward_terms)?;
        let maps = forward_terms
            .iter()
            .zip(&target.terms)
            .map(|(forward, target)| {
                sum_terms(
                    &forward.module,
                    &target.module,
                    target.indices.iter().enumerate().map(|(slot, _)| {
                        compose_three(
                            &forward.projective.split.projections()[slot],
                            &target.from_canonical[slot],
                            &target.split.inclusions()[slot],
                        )
                        .expect("canonical projective endpoints agree")
                    }),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let inverse_maps = forward_terms
            .iter()
            .zip(&target.terms)
            .map(|(forward, target)| {
                sum_terms(
                    &target.module,
                    &forward.module,
                    target.indices.iter().enumerate().map(|(slot, _)| {
                        compose_three(
                            &target.split.projections()[slot],
                            &target.to_canonical[slot],
                            &forward.projective.split.inclusions()[slot],
                        )
                        .expect("canonical projective endpoints agree")
                    }),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let counit = ChainMap::new(forward.complex(), target.complex(), maps)?;
        let inverse = ChainMap::new(target.complex(), forward.complex(), inverse_maps)?;
        ChainIsomorphism::new(counit, inverse)
    }
}

/// Rejected derived-equivalence certificate input or verification data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DerivedCertificateError {
    /// The tilting certificate does not verify.
    InvalidTilting,
    /// The target presentation does not verify.
    InvalidTarget,
    /// The target and tilting certificates use different source modules.
    DifferentSource,
    /// The projective resolution was not finite.
    ResolutionCut { at: usize },
    /// The named resolution term is not projective.
    ResolutionTermNotProjective { term: usize },
    /// The resolution does not form a bounded homological complex.
    ResolutionComplex(BoundedComplexError),
    /// A homotopy endomorphism space could not be constructed.
    Homotopy(ChainMapError),
    /// A nonzero self-Hom survives in the named degree.
    NonzeroSelfHom { degree: i32, dimension: usize },
    /// The degree-zero homotopy endomorphism space has the wrong dimension.
    DegreeZeroDimension {
        homotopy: usize,
        endomorphism: usize,
    },
    /// The degree-zero map to `End_A(T)` is not an algebra isomorphism.
    DegreeZeroIdentification { reason: String },
    /// The generation complex or one of its `add(T)` witnesses does not verify.
    Generation,
    /// Strict transport did not build from the target presentation.
    Transport(TransportError),
    /// A resolution width cannot be represented as a homological degree.
    DegreeOverflow { width: usize },
}

display_error! { DerivedCertificateError {
    Self::InvalidTilting => "tilting certificate does not verify";
    Self::InvalidTarget => "target presentation does not verify";
    Self::DifferentSource => "tilting and target certificates use different source modules";
    Self::ResolutionCut { at } => "tilting resolution was cut after {at} differentials";
    Self::ResolutionTermNotProjective { term } => "resolution term {term} is not projective";
    Self::ResolutionComplex(error) => "resolution complex rejected: {error}";
    Self::Homotopy(error) => "homotopy endomorphism space rejected: {error}";
    Self::NonzeroSelfHom { degree, dimension } => "homotopy self-Hom in degree {degree} has dimension {dimension}";
    Self::DegreeZeroDimension { homotopy, endomorphism } => "degree-zero homotopy dimension {homotopy} differs from End(T) dimension {endomorphism}";
    Self::DegreeZeroIdentification { reason } => "degree-zero End(T) identification failed: {reason}";
    Self::Generation => "generation complex or add(T) witnesses do not verify";
    Self::Transport(error) => "strict transport rejected: {error}";
    Self::DegreeOverflow { width } => "resolution width {width} does not fit in i32";
} }

error_source! { DerivedCertificateError {
    Self::ResolutionComplex(error) => Some(error),
    Self::Homotopy(error) => Some(error),
    Self::Transport(error) => Some(error),
    _ => None,
} }

/// One graded homotopy endomorphism space of the tilting resolution.
#[derive(Clone, Debug)]
pub struct GradedHomotopyEndomorphisms {
    degree: i32,
    quotient: ChainHomQuotient,
}

impl GradedHomotopyEndomorphisms {
    accessor_methods! {
        /// The target shift degree.
        pub degree() -> i32 = |this| this.degree;
        /// The deterministic homotopy quotient in this degree.
        pub quotient() -> &ChainHomQuotient = |this| &this.quotient;
    }

    /// Rechecks the stored quotient basis and null-homotopic subspace.
    pub fn verify(&self) -> bool {
        self.quotient.verify()
    }
}

/// The checked degree-zero map from homotopy endomorphisms to `End_A(T)`.
#[derive(Clone, Debug)]
pub struct DegreeZeroEndIdentification {
    quotient: ChainHomQuotient,
    coordinates: DenseMat,
}

impl DegreeZeroEndIdentification {
    accessor_methods! {
        /// The degree-zero homotopy endomorphism quotient.
        pub quotient() -> &ChainHomQuotient = |this| &this.quotient;
        /// Rows map quotient-basis coordinates to `End_A(T)` coordinates.
        pub coordinates() -> &DenseMat = |this| &this.coordinates;
    }
}

fn induced_endomorphism_coordinates(
    resolution: &ProjectiveResolution,
    map: &ChainMap,
    target: &VerifiedTargetPresentation,
) -> Result<Vec<crate::field::Fp>, DerivedCertificateError> {
    let endo = target.endo();
    let hom = HomSpace::new(&resolution.terms[0], target.source()).map_err(|error| {
        DerivedCertificateError::DegreeZeroIdentification {
            reason: format!("augmentation Hom space failed: {error}"),
        }
    })?;
    let rows: Vec<Vec<crate::field::Fp>> = endo
        .basis()
        .iter()
        .map(|basis| {
            resolution
                .augmentation
                .then(basis)
                .and_then(|map| hom.coords(&map).map_err(|_| HomError::EndpointMismatch))
        })
        .collect::<Result<_, _>>()
        .map_err(|error| DerivedCertificateError::DegreeZeroIdentification {
            reason: format!("End(T) action on the augmentation failed: {error}"),
        })?;
    let lift = DenseMat::from_rows_with_cols(&rows, hom.dim());
    let component = map
        .component(0)
        .map_err(DerivedCertificateError::Homotopy)?;
    let desired = component
        .then(&resolution.augmentation)
        .and_then(|map| hom.coords(&map).map_err(|_| HomError::EndpointMismatch))
        .map_err(|error| DerivedCertificateError::DegreeZeroIdentification {
            reason: format!("chain map did not descend along the augmentation: {error}"),
        })?;
    lift.transpose()
        .solve(&desired, &endo.field())
        .ok_or_else(|| DerivedCertificateError::DegreeZeroIdentification {
            reason: "chain map has no induced endomorphism of T".to_string(),
        })
}

fn degree_zero_identification(
    resolution_complex: &BoundedComplex,
    resolution: &ProjectiveResolution,
    target: &VerifiedTargetPresentation,
    quotient: &ChainHomQuotient,
) -> Result<DegreeZeroEndIdentification, DerivedCertificateError> {
    let endo = target.endo();
    if quotient.dim() != endo.dim() {
        return Err(DerivedCertificateError::DegreeZeroDimension {
            homotopy: quotient.dim(),
            endomorphism: endo.dim(),
        });
    }
    let field = endo.field();
    let mut rows = Vec::with_capacity(quotient.dim());
    for index in 0..quotient.dim() {
        let mut coordinates = vec![field.zero(); quotient.dim()];
        coordinates[index] = field.one();
        rows.push(induced_endomorphism_coordinates(
            resolution,
            &quotient.representative(&coordinates),
            target,
        )?);
    }
    let coordinates = DenseMat::from_rows_with_cols(&rows, endo.dim());
    if coordinates.rank(&field) != endo.dim() {
        return Err(DerivedCertificateError::DegreeZeroIdentification {
            reason: "induced endomorphisms do not span End(T)".to_string(),
        });
    }
    for left in 0..quotient.dim() {
        let mut left_coordinates = vec![field.zero(); quotient.dim()];
        left_coordinates[left] = field.one();
        let left_map = quotient.representative(&left_coordinates);
        for right in 0..quotient.dim() {
            let mut right_coordinates = vec![field.zero(); quotient.dim()];
            right_coordinates[right] = field.one();
            let right_map = quotient.representative(&right_coordinates);
            let product = left_map
                .then(&right_map)
                .map_err(DerivedCertificateError::Homotopy)?;
            let quotient_product = quotient
                .reduce(&product)
                .map_err(DerivedCertificateError::Homotopy)?
                .0;
            let expected = row_times(&quotient_product, &coordinates, &field);
            let actual = induced_endomorphism_coordinates(resolution, &product, target)?;
            let direct = endo.multiply(coordinates.row(left), coordinates.row(right));
            if actual != expected || actual != direct {
                return Err(DerivedCertificateError::DegreeZeroIdentification {
                    reason: format!("product mismatch at quotient basis pair ({left}, {right})"),
                });
            }
        }
    }
    if !resolution_complex.verify() {
        return Err(DerivedCertificateError::ResolutionComplex(
            BoundedComplexError::Empty,
        ));
    }
    Ok(DegreeZeroEndIdentification {
        quotient: quotient.clone(),
        coordinates,
    })
}

/// A certificate for the bounded derived equivalence from a split tilting target.
pub struct DerivedEquivalenceCertificate {
    tilting: ClassicalTiltingModule,
    target: VerifiedTargetPresentation,
    resolution_complex: BoundedComplex,
    graded_homotopy: Vec<GradedHomotopyEndomorphisms>,
    degree_zero: DegreeZeroEndIdentification,
    transport: StrictTransport,
}

debug_fields!(DerivedEquivalenceCertificate |this| {
    "source_dim_vector" => this.tilting.module().dim_vector();
    "resolution_width" => this.tilting.projective_dimension();
    "graded_homotopy_spaces" => this.graded_homotopy.len();
});

impl DerivedEquivalenceCertificate {
    /// Builds the complete bounded derived-equivalence certificate.
    pub fn new(
        tilting: ClassicalTiltingModule,
        target: VerifiedTargetPresentation,
    ) -> Result<DerivedEquivalenceCertificate, DerivedCertificateError> {
        if !tilting.verify() {
            return Err(DerivedCertificateError::InvalidTilting);
        }
        if !target.verify() {
            return Err(DerivedCertificateError::InvalidTarget);
        }
        if !tilting.module().ptr_eq(target.source()) {
            return Err(DerivedCertificateError::DifferentSource);
        }
        let resolution = tilting.resolution();
        if let ResolutionEnd::Cut { at } = resolution.end {
            return Err(DerivedCertificateError::ResolutionCut { at });
        }
        for (term, module) in resolution.terms.iter().enumerate() {
            if !matches!(resolve(module, 0).end, ResolutionEnd::Finite) {
                return Err(DerivedCertificateError::ResolutionTermNotProjective { term });
            }
        }
        let resolution_complex =
            BoundedComplex::new(0, resolution.terms.clone(), resolution.maps.clone())
                .map_err(DerivedCertificateError::ResolutionComplex)?;
        let width = i32::try_from(tilting.projective_dimension()).map_err(|_| {
            DerivedCertificateError::DegreeOverflow {
                width: tilting.projective_dimension(),
            }
        })?;
        let mut graded_homotopy = Vec::with_capacity((width as usize).saturating_mul(2) + 1);
        let mut zero = None;
        for degree in -width..=width {
            let shifted = resolution_complex
                .shift(degree)
                .map_err(DerivedCertificateError::ResolutionComplex)?;
            let quotient = ChainHomSpace::new(&resolution_complex, &shifted)
                .map_err(DerivedCertificateError::Homotopy)?
                .quotient()
                .map_err(DerivedCertificateError::Homotopy)?;
            if degree != 0 && quotient.dim() != 0 {
                return Err(DerivedCertificateError::NonzeroSelfHom {
                    degree,
                    dimension: quotient.dim(),
                });
            }
            if degree == 0 {
                zero = Some(quotient.clone());
            }
            graded_homotopy.push(GradedHomotopyEndomorphisms { degree, quotient });
        }
        let zero = zero.expect("the degree range includes zero");
        let degree_zero =
            degree_zero_identification(&resolution_complex, resolution, &target, &zero)?;
        if !tilting.generation_complex().verify()
            || tilting.add_witnesses().len() + 1 != tilting.generation_complex().complex().len()
            || tilting
                .add_witnesses()
                .iter()
                .any(|witness| !witness.verify() || !witness.target().ptr_eq(tilting.module()))
        {
            return Err(DerivedCertificateError::Generation);
        }
        let transport =
            StrictTransport::new(target.clone()).map_err(DerivedCertificateError::Transport)?;
        Ok(DerivedEquivalenceCertificate {
            tilting,
            target,
            resolution_complex,
            graded_homotopy,
            degree_zero,
            transport,
        })
    }

    accessor_methods! {
        /// The verified classical tilting data.
        pub tilting() -> &ClassicalTiltingModule = |this| &this.tilting;
        /// The verified split target presentation.
        pub target() -> &VerifiedTargetPresentation = |this| &this.target;
        /// The bounded projective resolution as a homological complex.
        pub resolution_complex() -> &BoundedComplex = |this| &this.resolution_complex;
        /// The homotopy endomorphism quotients through the resolution width.
        pub graded_homotopy() -> &[GradedHomotopyEndomorphisms] = |this| &this.graded_homotopy;
        /// The checked degree-zero algebra identification.
        pub degree_zero_identification() -> &DegreeZeroEndIdentification = |this| &this.degree_zero;
        /// The strict `add(T)` and projective transport data.
        pub transport() -> &StrictTransport = |this| &this.transport;
    }

    /// Rechecks tilting, generation, target recovery, homotopy spaces, and transport.
    pub fn verify(&self) -> bool {
        if !self.tilting.verify()
            || !self.target.verify()
            || !self.tilting.module().ptr_eq(self.target.source())
            || !self.resolution_complex.verify()
            || self.tilting.resolution().end != ResolutionEnd::Finite
            || self
                .tilting
                .resolution()
                .terms
                .iter()
                .any(|term| !matches!(resolve(term, 0).end, ResolutionEnd::Finite))
        {
            return false;
        }
        let Ok(width) = i32::try_from(self.tilting.projective_dimension()) else {
            return false;
        };
        let Some(expected_count) = usize::try_from(width)
            .ok()
            .and_then(|width| width.checked_mul(2))
            .and_then(|width| width.checked_add(1))
        else {
            return false;
        };
        if self.graded_homotopy.len() != expected_count
            || !self
                .graded_homotopy
                .iter()
                .enumerate()
                .all(|(offset, space)| {
                    let degree = -width + offset as i32;
                    let expected = self
                        .resolution_complex
                        .shift(degree)
                        .ok()
                        .and_then(|shifted| {
                            DegreeRange::new(
                                self.resolution_complex.lower().min(shifted.lower()),
                                self.resolution_complex.upper().max(shifted.upper()),
                            )
                            .ok()
                            .and_then(|range| {
                                Some((
                                    self.resolution_complex.padded_to(range).ok()?,
                                    shifted.padded_to(range).ok()?,
                                ))
                            })
                        });
                    space.degree == degree
                        && space.verify()
                        && expected.is_some_and(|(source, target)| {
                            space.quotient.source().agrees_with(&source)
                                && space.quotient.target().agrees_with(&target)
                        })
                        && (degree == 0 || space.quotient.dim() == 0)
                })
        {
            return false;
        }
        let Some(zero) = self.graded_homotopy.iter().find(|space| space.degree == 0) else {
            return false;
        };
        let Ok(rebuilt_zero) = degree_zero_identification(
            &self.resolution_complex,
            self.tilting.resolution(),
            &self.target,
            &self.degree_zero.quotient,
        ) else {
            return false;
        };
        if !self.degree_zero.quotient.verify()
            || self.degree_zero.quotient.dim() != zero.quotient.dim()
            || rebuilt_zero.coordinates != self.degree_zero.coordinates
            || !self
                .degree_zero
                .quotient
                .source()
                .agrees_with(&self.resolution_complex)
            || !self
                .degree_zero
                .quotient
                .target()
                .agrees_with(&self.resolution_complex)
            || !self.tilting.generation_complex().verify()
            || self.tilting.add_witnesses().len() + 1
                != self.tilting.generation_complex().complex().len()
            || !self
                .tilting
                .add_witnesses()
                .iter()
                .zip(&self.tilting.generation_complex().complex().terms()[1..])
                .all(|(witness, term)| {
                    witness.verify()
                        && witness.module().ptr_eq(term)
                        && witness.target().ptr_eq(self.tilting.module())
                })
        {
            return false;
        }
        self.transport.verify()
            && self
                .transport
                .target()
                .source()
                .ptr_eq(self.target.source())
            && Arc::ptr_eq(self.transport.target().target(), self.target.target())
    }
}

#[derive(Clone, Debug)]
struct ForwardTerm {
    module: Module,
    homs: Vec<HomSpace>,
    projective: ProjectiveTerm,
    unit: Morphism,
    unit_inverse: Morphism,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{an_with_relations, linear_an};
    use crate::endo::EndoAlgebra;
    use crate::field::PrimeField;
    use crate::module::direct_sum;
    use crate::target::{TargetLimits, TargetPresentationOutcome, present_target};
    use crate::tilting::{ClassicalTiltingModule, ClassicalTiltingResult, TiltingLimits};

    fn f5() -> PrimeField {
        PrimeField::new(5).expect("5 is prime")
    }

    fn f2() -> PrimeField {
        PrimeField::new(2).expect("2 is prime")
    }

    fn regular(algebra: &Arc<Algebra>) -> Module {
        let projectives: Vec<Module> = (0..algebra.quiver().num_vertices())
            .map(|vertex| Module::projective(algebra, vertex))
            .collect();
        direct_sum(&projectives.iter().collect::<Vec<_>>()).0
    }

    fn strict_regular_transport() -> (StrictTransport, Module) {
        let algebra = linear_an(2, f5());
        let module = regular(&algebra);
        let limits = TiltingLimits {
            max_projective_dimension: 4,
            max_generation_steps: 8,
        };
        let ClassicalTiltingResult::Tilting(tilting) =
            ClassicalTiltingModule::classify(&module, limits).expect("fixture classifies")
        else {
            panic!("the regular module is classical tilting")
        };
        let TargetPresentationOutcome::Presented(target) =
            present_target(&tilting, &TargetLimits::default()).expect("target completes")
        else {
            panic!("the regular target is split")
        };
        (
            StrictTransport::new(target).expect("strict transport builds"),
            module,
        )
    }

    fn regular_certificate_inputs() -> (ClassicalTiltingModule, VerifiedTargetPresentation) {
        let algebra = linear_an(2, f5());
        let module = regular(&algebra);
        let limits = TiltingLimits {
            max_projective_dimension: 4,
            max_generation_steps: 8,
        };
        let ClassicalTiltingResult::Tilting(tilting) =
            ClassicalTiltingModule::classify(&module, limits).expect("fixture classifies")
        else {
            panic!("the regular module is classical tilting")
        };
        let TargetPresentationOutcome::Presented(target) =
            present_target(&tilting, &TargetLimits::default()).expect("target completes")
        else {
            panic!("the regular target is split")
        };
        (tilting, target)
    }

    #[test]
    fn regular_generator_transports_one_term_in_both_directions() {
        let (transport, module) = strict_regular_transport();
        let basic = BasicDecomposition::new(&module).expect("regular module is basic");
        let witness = AddClosureWitness::from_module(&module, &basic)
            .expect("membership decomposes")
            .expect("T lies in add(T)");
        let source = AddTComplex::new(
            BoundedComplex::new(0, vec![module], Vec::new()).expect("one term is a complex"),
            vec![witness],
        )
        .expect("witnessed source builds");
        let target = transport
            .forward(&source)
            .expect("forward transport builds");
        assert!(target.verify());
        let back = transport
            .reverse(&target)
            .expect("reverse transport builds");
        assert!(back.verify());
        assert!(transport.source_round_trip(&source).is_ok());
        assert!(transport.target_round_trip(&target).is_ok());
    }

    #[test]
    fn regular_generator_transports_a_chain_map_and_round_trip() {
        let (transport, module) = strict_regular_transport();
        let basic = BasicDecomposition::new(&module).expect("regular module is basic");
        let witness = AddClosureWitness::from_module(&module, &basic)
            .expect("membership decomposes")
            .expect("T lies in add(T)");
        let complex = BoundedComplex::new(
            0,
            vec![module.clone(), module.clone()],
            vec![identity(&module)],
        )
        .expect("identity is a one-step complex");
        let source = AddTComplex::new(complex.clone(), vec![witness.clone(), witness])
            .expect("witnessed source builds");
        let map = ChainMap::identity(&complex);
        assert!(transport.forward_chain_map(&source, &source, &map).is_ok());
        let target = transport
            .forward(&source)
            .expect("forward transport builds");
        assert!(
            transport
                .reverse_chain_map(&target, &target, &ChainMap::identity(target.complex()))
                .is_ok()
        );
        assert!(transport.source_round_trip(&source).is_ok());
    }

    #[test]
    fn transport_normalizes_unequal_chain_supports_before_mapping() {
        let (transport, module) = strict_regular_transport();
        let basic = BasicDecomposition::new(&module).expect("regular module is basic");
        let witness = AddClosureWitness::from_module(&module, &basic)
            .expect("membership decomposes")
            .expect("T lies in add(T)");
        let low = AddTComplex::new(
            BoundedComplex::new(0, vec![module.clone()], Vec::new())
                .expect("one term is a complex"),
            vec![witness.clone()],
        )
        .expect("lower source builds");
        let high = AddTComplex::new(
            BoundedComplex::new(1, vec![module.clone()], Vec::new())
                .expect("one term is a complex"),
            vec![witness],
        )
        .expect("upper source builds");
        let map = ChainMap::zero(low.complex(), high.complex())
            .expect("the offset zero map is a chain map");
        assert_eq!((map.range().lower(), map.range().upper()), (0, 1));
        let target_map = transport
            .forward_chain_map(&low, &high, &map)
            .expect("forward map accepts padded support");
        assert!(target_map.verify());
        let low_target = transport.forward(&low).expect("lower target builds");
        let high_target = transport.forward(&high).expect("upper target builds");
        let reverse_map = transport
            .reverse_chain_map(&low_target, &high_target, &target_map)
            .expect("reverse map accepts padded support");
        assert!(reverse_map.verify());

        let homotopy = ChainHomotopy::new(low.complex(), high.complex(), vec![identity(&module)])
            .expect("the offset identity is a homotopy component");
        let target_homotopy = transport
            .forward_homotopy(&low, &high, &homotopy)
            .expect("forward homotopy accepts padded support");
        assert!(target_homotopy.verify());
        let reverse_homotopy = transport
            .reverse_homotopy(&low_target, &high_target, &target_homotopy)
            .expect("reverse homotopy accepts padded support");
        assert!(reverse_homotopy.verify());

        assert!(transport.forward_cone(&low, &high, &map).is_ok());
        assert!(
            transport
                .reverse_cone(&low_target, &high_target, &target_map)
                .is_ok()
        );
    }

    #[test]
    fn regular_generator_has_a_verified_derived_certificate() {
        let (tilting, target) = regular_certificate_inputs();
        let certificate = DerivedEquivalenceCertificate::new(tilting, target)
            .expect("regular generator has a certificate");
        assert!(certificate.verify());
        assert_eq!(certificate.graded_homotopy().len(), 1);
        assert_eq!(
            certificate.degree_zero_identification().quotient().dim(),
            certificate.target().endo().dim()
        );
    }

    #[test]
    fn projective_dimension_one_tilting_module_has_a_certificate() {
        let algebra = linear_an(2, f5());
        let p0 = Module::projective(&algebra, 0);
        let s0 = Module::simple(&algebra, 0);
        let module = direct_sum(&[&p0, &s0]).0;
        let limits = TiltingLimits {
            max_projective_dimension: 4,
            max_generation_steps: 8,
        };
        let ClassicalTiltingResult::Tilting(tilting) =
            ClassicalTiltingModule::classify(&module, limits).expect("fixture classifies")
        else {
            panic!("the fixture is classical tilting")
        };
        let TargetPresentationOutcome::Presented(target) =
            present_target(&tilting, &TargetLimits::default()).expect("target completes")
        else {
            panic!("the tilting target is split")
        };
        let certificate = DerivedEquivalenceCertificate::new(tilting, target)
            .expect("projective-dimension-one fixture has a certificate");
        assert!(certificate.verify());
        assert_eq!(certificate.graded_homotopy().len(), 3);
    }

    #[test]
    fn projective_dimension_two_fixture_has_a_certificate_over_f2_and_f5() {
        for field in [f2(), f5()] {
            let algebra = an_with_relations(3, &[(0, 2)], field).expect("ab is a valid relation");
            let injectives: Vec<Module> = (0..3)
                .map(|vertex| Module::injective(&algebra, vertex))
                .collect();
            let module = direct_sum(&injectives.iter().collect::<Vec<_>>()).0;
            let limits = TiltingLimits {
                max_projective_dimension: 4,
                max_generation_steps: 8,
            };
            let ClassicalTiltingResult::Tilting(tilting) =
                ClassicalTiltingModule::classify(&module, limits).expect("fixture classifies")
            else {
                panic!("the dual fixture is classical tilting")
            };
            assert_eq!(
                tilting.projective_dimension(),
                2,
                "over F_{}",
                field.modulus()
            );
            let TargetPresentationOutcome::Presented(target) =
                present_target(&tilting, &TargetLimits::default()).expect("target completes")
            else {
                panic!("the dual target is split")
            };
            let certificate = DerivedEquivalenceCertificate::new(tilting, target)
                .expect("pd2 fixture has a certificate");
            assert!(certificate.verify(), "over F_{}", field.modulus());
            assert_eq!(certificate.graded_homotopy().len(), 5);
            assert!(
                certificate
                    .graded_homotopy()
                    .iter()
                    .filter(|space| space.degree() != 0)
                    .all(|space| space.quotient().dim() == 0)
            );
        }
    }

    #[test]
    fn nonidentity_two_term_complex_and_chain_map_round_trip() {
        let (transport, module) = strict_regular_transport();
        let endo = EndoAlgebra::new(&module);
        let differential = endo
            .basis()
            .iter()
            .find(|map| !map.is_zero() && **map != identity(&module))
            .expect("A_2 has a nonidentity endomorphism")
            .clone();
        let complex = BoundedComplex::new(
            0,
            vec![module.clone(), module.clone()],
            vec![differential.clone()],
        )
        .expect("one differential forms a complex");
        let map = ChainMap::new(&complex, &complex, vec![differential.clone(), differential])
            .expect("the same endomorphism in both degrees is a chain map");
        let basic = BasicDecomposition::new(&module).expect("regular module is basic");
        let witness = AddClosureWitness::from_module(&module, &basic)
            .expect("membership decomposes")
            .expect("T lies in add(T)");
        let source = AddTComplex::new(complex, vec![witness.clone(), witness])
            .expect("witnessed source builds");
        let target_map = transport
            .forward_chain_map(&source, &source, &map)
            .expect("forward map transport builds");
        assert!(target_map.verify());
        let target = transport.forward(&source).expect("forward complex builds");
        let target_map_again = transport
            .forward_chain_map(&source, &source, &map)
            .expect("independent forward map transport builds");
        let source_product = map.then(&map).expect("source maps compose");
        let target_product = transport
            .forward_chain_map(&source, &source, &source_product)
            .expect("forward product transport builds");
        assert!(
            target_product.agrees_with(
                &target_map
                    .then(&target_map_again)
                    .expect("independent forward images compose")
            )
        );
        let reverse_map = transport
            .reverse_chain_map(&target, &target, &target_map)
            .expect("reverse map transport builds");
        assert!(reverse_map.verify());
        let reverse_map_again = transport
            .reverse_chain_map(&target, &target, &target_map_again)
            .expect("independent reverse map transport builds");
        let reverse_product = transport
            .reverse_chain_map(&target, &target, &target_product)
            .expect("reverse product transport builds");
        assert!(
            reverse_product.agrees_with(
                &reverse_map
                    .then(&reverse_map_again)
                    .expect("independent reverse images compose")
            )
        );
        let homotopy = ChainHomotopy::new(
            source.complex(),
            source.complex(),
            vec![zero_morphism(&module, &module).expect("zero map exists")],
        )
        .expect("zero component is a homotopy");
        let target_homotopy = transport
            .forward_homotopy(&source, &source, &homotopy)
            .expect("forward homotopy transport builds");
        assert!(target_homotopy.verify());
        let reverse_homotopy = transport
            .reverse_homotopy(&target, &target, &target_homotopy)
            .expect("reverse homotopy transport builds");
        assert!(reverse_homotopy.verify());
        assert!(transport.forward_cone(&source, &source, &map).is_ok());
        assert!(
            transport
                .reverse_cone(&target, &target, &target_map)
                .is_ok()
        );
        assert!(transport.forward_shift(&source, 2).is_ok());
        assert!(transport.reverse_shift(&target, -2).is_ok());
        assert!(transport.forward_direct_sum(&[&source, &source]).is_ok());
        assert!(transport.reverse_direct_sum(&[&target, &target]).is_ok());
        assert!(transport.source_round_trip(&source).is_ok());
        assert!(transport.target_round_trip(&target).is_ok());
    }

    #[test]
    fn strict_domains_reject_the_first_bad_source_and_target_terms() {
        let (transport, module) = strict_regular_transport();
        let algebra = module.algebra().clone();
        let p0 = Module::projective(&algebra, 0);
        let p0_basic = BasicDecomposition::new(&p0).expect("P_0 is basic");
        let wrong_witness = AddClosureWitness::from_module(&p0, &p0_basic)
            .expect("membership decomposes")
            .expect("P_0 lies in add(P_0)");
        let wrong_source = AddTComplex::new(
            BoundedComplex::new(0, vec![p0], Vec::new()).expect("one term is a complex"),
            vec![wrong_witness],
        )
        .expect("the unrelated witness is internally valid");
        assert!(matches!(
            transport.forward(&wrong_source),
            Err(TransportError::SourceWitnessTarget { term: 0 })
        ));

        let target_algebra = transport.target().target();
        let nonprojective = (0..target_algebra.quiver().num_vertices())
            .map(|vertex| Module::simple(target_algebra, vertex))
            .find(|simple| matches!(resolve(simple, 0).end, ResolutionEnd::Cut { .. }))
            .expect("a nonsemisimple target has a nonprojective simple");
        assert!(matches!(
            transport.target_complex(
                BoundedComplex::new(0, vec![nonprojective], Vec::new())
                    .expect("one term is a complex")
            ),
            Err(TransportError::TargetTermNotProjective { term: 0 })
        ));
    }

    #[test]
    fn derived_certificate_and_transport_mutations_fail_verification() {
        let (tilting, target) = regular_certificate_inputs();
        let certificate = DerivedEquivalenceCertificate::new(tilting, target)
            .expect("regular generator has a certificate");
        assert!(certificate.verify());

        let mut changed = certificate;
        changed.graded_homotopy[0].degree = 1;
        assert!(!changed.verify());

        let (tilting, target) = regular_certificate_inputs();
        let mut changed = DerivedEquivalenceCertificate::new(tilting, target)
            .expect("regular generator has a certificate");
        let entry = changed.degree_zero.coordinates.get(0, 0);
        let field = changed.target.endo().field();
        changed
            .degree_zero
            .coordinates
            .set(0, 0, field.add(entry, field.one()));
        assert!(!changed.verify());

        let (transport, module) = strict_regular_transport();
        assert!(transport.verify());
        let basic = BasicDecomposition::new(&module).expect("regular module is basic");
        let witness = AddClosureWitness::from_module(&module, &basic)
            .expect("membership decomposes")
            .expect("T lies in add(T)");
        let source = AddTComplex::new(
            BoundedComplex::new(0, vec![module], Vec::new()).expect("one term is a complex"),
            vec![witness],
        )
        .expect("witnessed source builds");
        let mut target_complex = transport
            .forward(&source)
            .expect("forward transport builds");
        target_complex.terms[0].indices[0] = 1 - target_complex.terms[0].indices[0];
        assert!(!target_complex.verify());

        let mut changed = transport;
        changed.canonical_projectives[0] = Module::zero(changed.target.target());
        assert!(!changed.verify());
    }
}
