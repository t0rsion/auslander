use crate::certificate::Certificate;
use crate::completion::CompletionLimits;
use crate::equivalence_edge::DerivedEquivalenceEdge;
use crate::target::{TargetLimits, TargetWork};
use crate::tilting_complex::{
    ApproximationDirection, CertifiedTiltingComplex, ThickGenerationWitness, TiltingComplexLimits,
};

use super::DERIVED_ARTIFACT_SCHEMA;
use super::errors::ArtifactError;
use super::model::{ArtifactMutation, ArtifactParseLimits, DerivedArtifact};
use super::parser::RawArtifact;

impl DerivedArtifact {
    /// Builds an artifact from one verified equivalence edge.
    pub fn from_edge(edge: &DerivedEquivalenceEdge) -> Result<DerivedArtifact, ArtifactError> {
        if !edge.verify() {
            return Err(ArtifactError::InvalidEdge);
        }
        let mut mutations = Vec::new();
        collect_mutations(edge.tilting(), &mut mutations)?;
        let mut artifact = DerivedArtifact {
            source: edge.source().certificate().clone(),
            mutations,
            target: edge.target().certificate().clone(),
            tilting_limits: edge.tilting().limits(),
            target_limits: edge.target_presentation().limits().clone(),
            work: edge.target_presentation().work(),
            fingerprint: String::new(),
        };
        artifact.fingerprint = fingerprint(&artifact.canonical_without_fingerprint());
        Ok(artifact)
    }

    accessor_methods! {
        /// The source completion certificate.
        pub source_certificate() -> &Certificate = |this| &this.source;
        /// The ordered mutation recipe.
        pub mutations() -> &[ArtifactMutation] = |this| &this.mutations;
        /// The target completion certificate.
        pub target_certificate() -> &Certificate = |this| &this.target;
        /// The effective tilting limits.
        pub tilting_limits() -> TiltingComplexLimits = |this| this.tilting_limits;
        /// The effective target limits.
        pub target_limits() -> &TargetLimits = |this| &this.target_limits;
        /// The exact target-recovery work.
        pub work() -> TargetWork = |this| this.work;
        /// The canonical fingerprint.
        pub fingerprint() -> &str = |this| &this.fingerprint;
    }

    pub(super) fn canonical_without_fingerprint(&self) -> String {
        let mut output = String::new();
        output.push_str("{\"schema\":\"");
        output.push_str(DERIVED_ARTIFACT_SCHEMA);
        output.push_str("\",\"source\":");
        push_bytes(&mut output, self.source.to_canonical_json().as_bytes());
        output.push_str(",\"mutations\":[");
        for (index, mutation) in self.mutations.iter().enumerate() {
            if index != 0 {
                output.push(',');
            }
            output.push('[');
            output.push(match mutation.direction {
                ApproximationDirection::Left => '0',
                ApproximationDirection::Right => '1',
            });
            output.push(',');
            output.push_str(&mutation.summand.to_string());
            output.push(']');
        }
        output.push_str("],\"target\":");
        push_bytes(&mut output, self.target.to_canonical_json().as_bytes());
        output.push_str(",\"limits\":[");
        push_numbers(
            &mut output,
            &[
                self.tilting_limits.max_hom_spaces,
                self.target_limits.max_endo_dimension,
                self.target_limits.max_radical_products,
                self.target_limits.max_paths,
                self.target_limits.max_relation_terms,
                self.target_limits.completion.max_basis,
                self.target_limits.completion.max_word_len,
                self.target_limits.completion.max_steps,
                self.target_limits.completion.max_origin_terms,
                self.target_limits.completion.max_ambiguities,
            ],
        );
        output.push_str("],\"work\":[");
        push_numbers(
            &mut output,
            &[
                self.work.endo_dimension,
                self.work.radical_products,
                self.work.paths,
                self.work.relation_terms,
            ],
        );
        output.push(']');
        output
    }

    /// Serializes the artifact to byte-exact canonical JSON.
    pub fn to_canonical_json(&self) -> String {
        let mut output = self.canonical_without_fingerprint();
        output.push_str(",\"fingerprint\":\"");
        output.push_str(&self.fingerprint);
        output.push_str("\"}");
        output
    }

    /// Parses the bounded artifact envelope and both strict certificates.
    pub fn from_json(
        text: &str,
        limits: ArtifactParseLimits,
    ) -> Result<DerivedArtifact, ArtifactError> {
        if text.len() > limits.max_input_bytes {
            return Err(ArtifactError::ParseLimit {
                path: "$".to_string(),
                used: text.len(),
                limit: limits.max_input_bytes,
            });
        }
        let raw = RawArtifact::parse(text, limits)?;
        let source_text = String::from_utf8(raw.source).map_err(|_| ArtifactError::Syntax {
            byte: 0,
            message: "source certificate bytes are not UTF-8".to_string(),
        })?;
        let target_text = String::from_utf8(raw.target).map_err(|_| ArtifactError::Syntax {
            byte: 0,
            message: "target certificate bytes are not UTF-8".to_string(),
        })?;
        let source =
            Certificate::from_json(&source_text).map_err(|error| ArtifactError::Certificate {
                path: "$.source".to_string(),
                message: error.to_string(),
            })?;
        let target =
            Certificate::from_json(&target_text).map_err(|error| ArtifactError::Certificate {
                path: "$.target".to_string(),
                message: error.to_string(),
            })?;
        let tilting_limits = TiltingComplexLimits {
            max_hom_spaces: raw.limits[0],
        };
        let target_limits = TargetLimits {
            max_endo_dimension: raw.limits[1],
            max_radical_products: raw.limits[2],
            max_paths: raw.limits[3],
            max_relation_terms: raw.limits[4],
            completion: CompletionLimits {
                max_basis: raw.limits[5],
                max_word_len: raw.limits[6],
                max_steps: raw.limits[7],
                max_origin_terms: raw.limits[8],
                max_ambiguities: raw.limits[9],
            },
        };
        Ok(DerivedArtifact {
            source,
            mutations: raw.mutations,
            target,
            tilting_limits,
            target_limits,
            work: TargetWork {
                endo_dimension: raw.work[0],
                radical_products: raw.work[1],
                paths: raw.work[2],
                relation_terms: raw.work[3],
            },
            fingerprint: raw.fingerprint,
        })
    }

    /// Whether the fingerprint matches every preceding canonical field.
    pub fn has_valid_fingerprint(&self) -> bool {
        self.fingerprint == fingerprint(&self.canonical_without_fingerprint())
    }
}

fn collect_mutations(
    tilting: &CertifiedTiltingComplex,
    output: &mut Vec<ArtifactMutation>,
) -> Result<(), ArtifactError> {
    match tilting.generation() {
        ThickGenerationWitness::Regular => Ok(()),
        ThickGenerationWitness::Mutation {
            parent,
            approximation,
        } => {
            collect_mutations(parent, output)?;
            output.push(ArtifactMutation {
                direction: approximation.direction(),
                summand: approximation.replaced(),
            });
            Ok(())
        }
    }
}

fn push_bytes(output: &mut String, bytes: &[u8]) {
    output.push('[');
    for (index, byte) in bytes.iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        output.push_str(&byte.to_string());
    }
    output.push(']');
}

fn push_numbers(output: &mut String, values: &[usize]) {
    for (index, value) in values.iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        output.push_str(&value.to_string());
    }
}

pub(super) fn fingerprint(text: &str) -> String {
    let mut value = 0xcbf29ce484222325u64;
    for byte in text.bytes() {
        value ^= u64::from(byte);
        value = value.wrapping_mul(0x100000001b3);
    }
    format!("{value:016x}")
}
