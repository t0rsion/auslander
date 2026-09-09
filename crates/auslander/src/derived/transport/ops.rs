use crate::basic::AddClosureWitness;
use crate::hom::Morphism;
use crate::homotopy::{BoundedComplex, ChainHomotopy, ChainMap, DegreeRange};
use crate::module::Module;

use super::{
    AddTComplex, ChainIsomorphism, ForwardTerm, ProjectiveTargetComplex, ProjectiveTerm,
    StrictTransport, TransportError, agrees_after_padding, compose_three, sum_terms,
    transported_components,
};

impl StrictTransport {
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
        let (unit_maps, inverse_maps): (Vec<_>, Vec<_>) = forward_terms
            .iter()
            .map(|term| (term.unit.clone(), term.unit_inverse.clone()))
            .unzip();
        let unit = ChainMap::new(source.complex(), reverse.complex(), unit_maps)?;
        let inverse = ChainMap::new(reverse.complex(), source.complex(), inverse_maps)?;
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
