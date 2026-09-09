use std::sync::Arc;

use crate::basic::{AddClosureWitness, BasicDecomposition};
use crate::decompose::{Split, direct_sum_or_zero, inverse_morphism};
use crate::hom::{Morphism, identity};
use crate::homotopy::BoundedComplex;
use crate::homspace::HomSpace;
use crate::iso::{IsoOutcome, is_isomorphic};
use crate::linalg::DenseMat;
use crate::module::{Module, same_representation, summand_sum};
use crate::target::VerifiedTargetPresentation;

use super::{
    AddTComplex, ForwardSummandLists, ForwardTerm, ProjectiveTargetComplex, ProjectiveTerm,
    SourceTerm, StrictTransport, TransportError, compose_three, coordinate_matrix, rebase_morphism,
    sum_terms,
};

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

    pub(super) fn target_summands(&self) -> &[Module] {
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
        let (total, inclusions, projections) =
            direct_sum_or_zero(self.target.source().algebra(), parts.iter());
        let split = Split::new(&total, parts.clone(), inclusions, projections)?;
        let to_target: Vec<Morphism> = parts.iter().map(identity).collect();
        let from_target = to_target.clone();
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
                coordinate_matrix(&homs[source], &homs[destination], |row| {
                    Ok(precompose.then(&homs[source].basis_morphism(row))?)
                })
            })
            .collect::<Result<_, TransportError>>()?;
        Ok((Module::new(self.target.target().clone(), dims, maps)?, homs))
    }

    pub(super) fn forward_morphism(
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
                coordinate_matrix(source, target, |row| {
                    Ok(source.basis_morphism(row).then(map)?)
                })
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

    fn forward_summand(
        &self,
        source: &SourceTerm,
        slot: usize,
        index: usize,
        module: &Module,
        homs: &[HomSpace],
    ) -> Result<(Morphism, Morphism), TransportError> {
        let (summand_image, summand_homs) = self.forward_module(&source.split.summands()[slot])?;
        let projection = self.forward_morphism(
            module,
            homs,
            &summand_image,
            &summand_homs,
            &source.split.projections()[slot],
        )?;
        let inclusion = self.forward_morphism(
            &summand_image,
            &summand_homs,
            module,
            homs,
            &source.split.inclusions()[slot],
        )?;
        let (target_image, target_homs) = self.forward_module(&self.target_summands()[index])?;
        let to_target = self.forward_morphism(
            &summand_image,
            &summand_homs,
            &target_image,
            &target_homs,
            &source.to_target[slot],
        )?;
        let from_target = self.forward_morphism(
            &target_image,
            &target_homs,
            &summand_image,
            &summand_homs,
            &source.from_target[slot],
        )?;
        let (to_projective, from_projective) =
            self.canonical_forward_iso(index, &target_image, &target_homs)?;
        let projection = compose_three(&projection, &to_target, &to_projective)?;
        let inclusion = compose_three(&from_projective, &from_target, &inclusion)?;
        Ok((projection, inclusion))
    }

    fn forward_summands(
        &self,
        source: &SourceTerm,
        module: &Module,
        homs: &[HomSpace],
    ) -> Result<ForwardSummandLists, TransportError> {
        let mut projectives = Vec::with_capacity(source.indices.len());
        let mut inclusions = Vec::with_capacity(source.indices.len());
        let mut projections = Vec::with_capacity(source.indices.len());
        for (slot, &index) in source.indices.iter().enumerate() {
            let (projection, inclusion) =
                self.forward_summand(source, slot, index, module, homs)?;
            projectives.push(self.canonical_projectives[index].clone());
            projections.push(projection);
            inclusions.push(inclusion);
        }
        Ok((projectives, inclusions, projections))
    }

    pub(super) fn forward_term(&self, source: &SourceTerm) -> Result<ForwardTerm, TransportError> {
        let (module, homs) = self.forward_module(&source.module)?;
        let (projectives, inclusions, projections) =
            self.forward_summands(source, &module, &homs)?;
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
        let canonical_maps = (0..count)
            .map(|slot| identity(&self.canonical_projectives[indices[slot]]))
            .collect::<Vec<_>>();
        let projective = ProjectiveTerm {
            module: module.clone(),
            split,
            indices: indices.clone(),
            to_canonical: canonical_maps.clone(),
            from_canonical: canonical_maps,
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

    pub(super) fn projective_term(
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

    fn reverse_block(
        &self,
        source: &ProjectiveTerm,
        target: &ProjectiveTerm,
        map: &Morphism,
        left: usize,
        right: usize,
    ) -> Result<Morphism, TransportError> {
        let block = compose_three(
            &source.from_canonical[left],
            &source.split.inclusions()[left],
            map,
        )?
        .then(&target.split.projections()[right])?
        .then(&target.to_canonical[right])?;
        let source_block =
            self.target_block_to_source(&block, source.indices[left], target.indices[right])?;
        compose_three(
            &source.source.split.projections()[left],
            &source_block,
            &target.source.split.inclusions()[right],
        )
    }

    pub(super) fn reverse_morphism(
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
        for left in 0..source.indices.len() {
            for right in 0..target.indices.len() {
                terms.push(self.reverse_block(source, target, &map, left, right)?);
            }
        }
        sum_terms(&source.source.module, &target.source.module, terms)
    }

    pub(super) fn forward_terms(
        &self,
        source: &AddTComplex,
    ) -> Result<Vec<ForwardTerm>, TransportError> {
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

    pub(super) fn forward_complex_from_terms(
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
}
