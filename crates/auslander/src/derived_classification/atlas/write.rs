use crate::derived_artifact::push_mutation;
use crate::equivalence_discovery::DiscoveryStop;
use crate::portable::{
    fingerprint, open_header, push_ascii, push_escaped, push_list, push_number_fields,
    push_number_object, push_numbers, push_tagged_numbers, seal,
};

use super::super::{
    ClassSeparation, ClassificationLimits, DerivedClass, DerivedClassification,
    DerivedInvariantKind, MutationWalk, UnresolvedPair,
};
use super::errors::DerivedAtlasError;
use super::model::{
    AtlasClass, AtlasMerge, AtlasReading, AtlasSeparation, AtlasStop, DerivedAtlasArtifact,
    KIND_NAMES, encode_value, kind_name,
};
use super::{
    DERIVED_ATLAS_ARTIFACT_ENGINE, DERIVED_ATLAS_ARTIFACT_KIND, DERIVED_ATLAS_ARTIFACT_SCHEMA,
};

pub(super) const BAR_KEYS: [&str; 4] = [
    "max_tensor_tuples",
    "max_cochain_dim",
    "max_matrix_entries",
    "max_work_units",
];
pub(super) const DISCOVERY_KEYS: [&str; 5] = [
    "max_vertices",
    "max_directed_mutations",
    "max_total_terms",
    "max_matrix_entries",
    "max_hom_spaces",
];
pub(super) const TARGET_KEYS: [&str; 9] = [
    "max_endo_dimension",
    "max_radical_products",
    "max_paths",
    "max_relation_terms",
    "max_basis",
    "max_word_len",
    "max_steps",
    "max_origin_terms",
    "max_ambiguities",
];
pub(super) const WALK_KEYS: [&str; 6] = [
    "vertices",
    "blocked",
    "examined",
    "target_cuts",
    "unmatched",
    "merges",
];

impl DerivedClassification {
    /// The portable `derived-atlas-v1` artifact of this classification.
    ///
    /// Errors with [`DerivedAtlasError::EmptyFamily`] for an empty family,
    /// and with [`DerivedAtlasError::CancelledReading`] when cancellation
    /// stopped an invariant: the verifier recomputes every reading and
    /// cannot reproduce a cancelled one. See
    /// [`super::verify_derived_atlas_artifact`].
    pub fn to_artifact(&self) -> Result<DerivedAtlasArtifact, DerivedAtlasError> {
        let first = self.family.first().ok_or(DerivedAtlasError::EmptyFamily)?;
        let invariants = self.invariants.iter().enumerate().map(|(member, record)| {
            let readings = DerivedInvariantKind::ALL.iter();
            let readings = readings.map(|&kind| AtlasReading::from_reading(record.reading(kind)));
            let readings: Option<Vec<_>> = readings.collect();
            readings.ok_or(DerivedAtlasError::CancelledReading { member })
        });
        let mut artifact = DerivedAtlasArtifact {
            field: first.field().modulus(),
            limits: self.limits.clone(),
            members: self
                .family
                .iter()
                .map(|a| a.certificate().clone())
                .collect(),
            invariants: invariants.collect::<Result<_, _>>()?,
            classes: self.classes.iter().map(atlas_class).collect(),
            separations: self.separations.iter().map(atlas_separation).collect(),
            unresolved: self.unresolved.clone(),
            walks: self.walks.clone(),
            status: self.status(),
            fingerprint: String::new(),
        };
        artifact.fingerprint = fingerprint(&artifact.canonical_without_fingerprint());
        Ok(artifact)
    }
}

fn atlas_class(class: &DerivedClass) -> AtlasClass {
    let merges = class.merges.iter().map(|merge| AtlasMerge {
        source: merge.source,
        member: merge.member,
        recipe: merge.recipe.clone(),
        vertex_map: merge.isomorphism.vertex_map.clone(),
        arrow_images: merge
            .isomorphism
            .arrow_images
            .iter()
            .map(|image| image.iter().map(|value| value.raw()).collect())
            .collect(),
    });
    AtlasClass {
        members: class.members.clone(),
        merges: merges.collect(),
    }
}

fn atlas_separation(separation: &ClassSeparation) -> AtlasSeparation {
    let witness = &separation.witness;
    AtlasSeparation {
        classes: separation.classes,
        members: separation.members,
        kind: witness.kind(),
        left: encode_value(witness.left_value()),
        right: encode_value(witness.right_value()),
    }
}

impl DerivedAtlasArtifact {
    pub(super) fn canonical_without_fingerprint(&self) -> String {
        let mut output = open_header([
            DERIVED_ATLAS_ARTIFACT_SCHEMA,
            DERIVED_ATLAS_ARTIFACT_KIND,
            DERIVED_ATLAS_ARTIFACT_ENGINE,
        ]);
        output.push_str(",\"field\":");
        output.push_str(&self.field.to_string());
        output.push_str(",\"limits\":");
        push_limits(&mut output, &self.limits);
        output.push_str(",\"members\":");
        push_list(&mut output, &self.members, |output, certificate| {
            push_escaped(output, certificate.to_canonical_json().as_bytes());
        });
        output.push_str(",\"invariants\":");
        push_list(&mut output, &self.invariants, |output, readings| {
            let rows: Vec<_> = KIND_NAMES.iter().zip(readings).collect();
            push_list(output, &rows, |output, (name, reading)| {
                push_reading(output, name, reading);
            });
        });
        output.push_str(",\"classes\":");
        push_list(&mut output, &self.classes, push_class);
        output.push_str(",\"separations\":");
        push_list(&mut output, &self.separations, push_separation);
        output.push_str(",\"unresolved\":");
        push_list(&mut output, &self.unresolved, push_unresolved);
        output.push_str(",\"walks\":");
        push_list(&mut output, &self.walks, push_walk);
        output.push_str(",\"status\":");
        push_ascii(&mut output, self.status.as_str());
        output
    }

    /// Serializes the atlas to byte-exact canonical JSON.
    pub fn to_canonical_json(&self) -> String {
        seal(self.canonical_without_fingerprint(), &self.fingerprint)
    }

    /// Whether the fingerprint matches every preceding canonical field.
    pub fn has_valid_fingerprint(&self) -> bool {
        self.fingerprint == fingerprint(&self.canonical_without_fingerprint())
    }
}

pub(super) fn stop_name(stop: AtlasStop) -> &'static str {
    match stop {
        AtlasStop::Overflow => "overflow",
        AtlasStop::BarCut => "bar_cut",
    }
}

fn push_limits(output: &mut String, limits: &ClassificationLimits) {
    let (invariants, bar) = (&limits.invariants, &limits.invariants.bar);
    output.push_str("{\"invariants\":{\"hochschild_degree\":");
    output.push_str(&invariants.hochschild_degree.to_string());
    let values = [
        bar.max_tensor_tuples,
        bar.max_cochain_dim,
        bar.max_matrix_entries,
        bar.max_work_units,
    ];
    let fields: Vec<(&str, u64)> = BAR_KEYS.into_iter().zip(values).collect();
    push_number_fields(output, &fields);
    let discovery = &limits.discovery;
    let values = [
        discovery.max_vertices,
        discovery.max_directed_mutations,
        discovery.max_total_terms,
        discovery.max_matrix_entries,
        discovery.tilting.max_hom_spaces,
    ];
    let fields: Vec<(&str, u64)> = DISCOVERY_KEYS.into_iter().zip(values).collect();
    output.push_str("},\"discovery\":");
    push_number_object(output, &fields);
    output.pop();
    push_number_fields(output, &[("through_silting", discovery.through_silting)]);
    output.push('}');
    let (target, completion) = (&limits.target, &limits.target.completion);
    let values = [
        target.max_endo_dimension,
        target.max_radical_products,
        target.max_paths,
        target.max_relation_terms,
        completion.max_basis,
        completion.max_word_len,
        completion.max_steps,
        completion.max_origin_terms,
        completion.max_ambiguities,
    ];
    let fields: Vec<(&str, u64)> = TARGET_KEYS.into_iter().zip(values).collect();
    output.push_str(",\"target\":");
    push_number_object(output, &fields);
    output.push('}');
}

fn push_reading(output: &mut String, name: &str, reading: &AtlasReading) {
    output.push_str("{\"kind\":");
    push_ascii(output, name);
    match reading {
        AtlasReading::Finished(value) => {
            output.push_str(",\"reading\":\"finished\",\"value\":");
            push_numbers(output, value);
        }
        AtlasReading::Stopped(stop) => {
            output.push_str(",\"reading\":\"stopped\",\"stop\":");
            push_ascii(output, stop_name(*stop));
        }
        AtlasReading::NotApplicable => output.push_str(",\"reading\":\"not_applicable\""),
    }
    output.push('}');
}

fn push_pair(output: &mut String, (left, right): (usize, usize)) {
    push_numbers(output, &[left, right]);
}

fn push_class(output: &mut String, class: &AtlasClass) {
    output.push_str("{\"members\":");
    push_numbers(output, &class.members);
    output.push_str(",\"merges\":");
    push_list(output, &class.merges, |output, merge| {
        output.push_str("{\"source\":");
        output.push_str(&merge.source.to_string());
        output.push_str(",\"member\":");
        output.push_str(&merge.member.to_string());
        output.push_str(",\"recipe\":");
        push_list(output, &merge.recipe, push_mutation);
        output.push_str(",\"vertex_map\":");
        push_numbers(output, &merge.vertex_map);
        output.push_str(",\"arrow_images\":");
        push_list(output, &merge.arrow_images, |output, image| {
            push_numbers(output, image);
        });
        output.push('}');
    });
    output.push('}');
}

fn push_separation(output: &mut String, separation: &AtlasSeparation) {
    output.push_str("{\"classes\":");
    push_pair(output, separation.classes);
    output.push_str(",\"members\":");
    push_pair(output, separation.members);
    output.push_str(",\"kind\":");
    push_ascii(output, kind_name(separation.kind));
    output.push_str(",\"left\":");
    push_numbers(output, &separation.left);
    output.push_str(",\"right\":");
    push_numbers(output, &separation.right);
    output.push('}');
}

fn push_unresolved(output: &mut String, pair: &UnresolvedPair) {
    output.push_str("{\"classes\":");
    push_pair(output, pair.classes);
    output.push_str(",\"walks\":");
    push_numbers(output, &pair.walks);
    output.push('}');
}

fn push_walk(output: &mut String, walk: &MutationWalk) {
    output.push_str("{\"member\":");
    output.push_str(&walk.member.to_string());
    output.push_str(",\"stop\":");
    let (name, values) = stop_values(&walk.stop);
    let keys = stop_keys(name).expect("stop_keys names every discovery stop");
    let fields: Vec<_> = keys.iter().copied().zip(values).collect();
    push_tagged_numbers(output, name, &fields);
    let counts = [
        walk.vertices,
        walk.blocked,
        walk.examined,
        walk.target_cuts,
        walk.unmatched,
        walk.merges,
    ];
    let counts: Vec<_> = WALK_KEYS.into_iter().zip(counts).collect();
    push_number_fields(output, &counts);
    output.push('}');
}

/// The portable name and the field values of one discovery stop, in the
/// order of [`stop_keys`]. [`stop_from`] inverts it.
fn stop_values(stop: &DiscoveryStop) -> (&'static str, Vec<u64>) {
    match *stop {
        DiscoveryStop::ExhaustedFrontier => ("exhausted_frontier", vec![]),
        DiscoveryStop::Cancelled {
            completed_mutations,
        } => ("cancelled", vec![completed_mutations]),
        DiscoveryStop::MutationLimit { completed, limit } => {
            ("mutation_limit", vec![completed, limit])
        }
        DiscoveryStop::VertexLimit { stored, limit } => ("vertex_limit", vec![stored, limit]),
        DiscoveryStop::TermLimit {
            stored,
            requested,
            limit,
        } => ("term_limit", vec![stored, requested, limit]),
        DiscoveryStop::MatrixLimit {
            stored,
            requested,
            limit,
        } => ("matrix_limit", vec![stored, requested, limit]),
    }
}

/// The field names of the discovery stop named `name`.
pub(super) fn stop_keys(name: &str) -> Option<&'static [&'static str]> {
    Some(match name {
        "exhausted_frontier" => &[],
        "cancelled" => &["completed_mutations"],
        "mutation_limit" => &["completed", "limit"],
        "vertex_limit" => &["stored", "limit"],
        "term_limit" | "matrix_limit" => &["stored", "requested", "limit"],
        _ => return None,
    })
}

/// The discovery stop named `name` with the fields `values`, in the order of
/// [`stop_keys`].
pub(super) fn stop_from(name: &str, values: &[u64]) -> DiscoveryStop {
    let value = |index: usize| values[index];
    match name {
        "exhausted_frontier" => DiscoveryStop::ExhaustedFrontier,
        "cancelled" => DiscoveryStop::Cancelled {
            completed_mutations: value(0),
        },
        "mutation_limit" => DiscoveryStop::MutationLimit {
            completed: value(0),
            limit: value(1),
        },
        "vertex_limit" => DiscoveryStop::VertexLimit {
            stored: value(0),
            limit: value(1),
        },
        "term_limit" => DiscoveryStop::TermLimit {
            stored: value(0),
            requested: value(1),
            limit: value(2),
        },
        _ => DiscoveryStop::MatrixLimit {
            stored: value(0),
            requested: value(1),
            limit: value(2),
        },
    }
}
