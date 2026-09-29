use crate::certificate::Certificate;
use crate::completion::CompletionLimits;
use crate::derived_artifact::read_mutation;
use crate::derived_invariant::InvariantLimits;
use crate::equivalence_discovery::{DiscoveryLimits, DiscoveryStop};
use crate::hochschild::BarLimits;
use crate::portable::{Cursor, CursorLimits, PortableError};
use crate::target::TargetLimits;
use crate::tilting_complex::TiltingComplexLimits;

use super::super::{ClassificationLimits, ClassificationStatus, MutationWalk, UnresolvedPair};
use super::errors::DerivedAtlasError;
use super::model::{
    AtlasClass, AtlasMerge, AtlasReading, AtlasSeparation, AtlasStop, DerivedAtlasArtifact,
    DerivedAtlasParseLimits, KIND_NAMES, kind_from_name,
};
use super::write::{
    BAR_KEYS, DISCOVERY_KEYS, TARGET_KEYS, WALK_KEYS, stop_from, stop_keys, stop_name,
};
use super::{
    DERIVED_ATLAS_ARTIFACT_ENGINE, DERIVED_ATLAS_ARTIFACT_KIND, DERIVED_ATLAS_ARTIFACT_SCHEMA,
};

type Parse<T> = Result<T, DerivedAtlasError>;

/// The longest name string: a header value, a kind, a stop, or a status.
const NAME_BYTES: usize = 64;

/// The stored members and their readings.
struct Family {
    members: Vec<Certificate>,
    invariants: Vec<Vec<AtlasReading>>,
}

/// The stored classes, pairs, and walks.
struct Settlement {
    classes: Vec<AtlasClass>,
    separations: Vec<AtlasSeparation>,
    unresolved: Vec<UnresolvedPair>,
    walks: Vec<MutationWalk>,
}

impl DerivedAtlasArtifact {
    /// Parses one atlas under `limits` without replay.
    ///
    /// Rejects unknown keys, reordered keys, and any text that does not
    /// serialize back to the same bytes. The fingerprint is checked by
    /// [`DerivedAtlasArtifact::verify`].
    pub fn from_json(text: &str, limits: DerivedAtlasParseLimits) -> Parse<DerivedAtlasArtifact> {
        let mut c = Cursor::new(
            text,
            CursorLimits {
                input_bytes: limits.max_input_bytes,
                integer_digits: limits.max_integer_digits,
                string_bytes: NAME_BYTES,
                numeric_values: limits.max_numeric_values,
                array_elements: limits.max_array_elements,
            },
        )?;
        let artifact = body(&mut c, &limits)?;
        c.token(b'}')?;
        c.end()?;
        c.fingerprint_shape(&artifact.fingerprint)?;
        match artifact.to_canonical_json() == text {
            true => Ok(artifact),
            false => Err(DerivedAtlasError::NonCanonical),
        }
    }
}

/// Every member of the open top-level object, in key order.
fn body(c: &mut Cursor, limits: &DerivedAtlasParseLimits) -> Parse<DerivedAtlasArtifact> {
    c.token(b'{')?;
    let expected = [
        DERIVED_ATLAS_ARTIFACT_SCHEMA,
        DERIVED_ATLAS_ARTIFACT_KIND,
        DERIVED_ATLAS_ARTIFACT_ENGINE,
    ];
    c.header::<DerivedAtlasError>("$.", expected)?;
    let field = c.next("field", |c| c.u64("$.field"))?;
    let classification = c.next("limits", classification_limits)?;
    let family = family(c, limits)?;
    let settled = settlement(c, limits)?;
    let status = c.next("status", status)?;
    let fingerprint = c.next("fingerprint", |c| c.string("$.fingerprint"))?;
    Ok(DerivedAtlasArtifact {
        field,
        limits: classification,
        members: family.members,
        invariants: family.invariants,
        classes: settled.classes,
        separations: settled.separations,
        unresolved: settled.unresolved,
        walks: settled.walks,
        status,
        fingerprint,
    })
}

fn classification_limits(c: &mut Cursor) -> Parse<ClassificationLimits> {
    c.token(b'{')?;
    c.key("invariants")?;
    let invariants = invariant_limits(c)?;
    let discovery = c.next("discovery", discovery_limits)?;
    let target = c.next("target", target_limits)?;
    c.token(b'}')?;
    Ok(ClassificationLimits {
        invariants,
        discovery,
        target,
    })
}

fn invariant_limits(c: &mut Cursor) -> Parse<InvariantLimits> {
    c.token(b'{')?;
    let path = "$.limits.invariants";
    c.key("hochschild_degree")?;
    let hochschild_degree = c.usize(path)?;
    c.token(b',')?;
    let [
        max_tensor_tuples,
        max_cochain_dim,
        max_matrix_entries,
        max_work_units,
    ] = c.uint_fields(path, BAR_KEYS)?;
    c.token(b'}')?;
    let bar = BarLimits {
        max_tensor_tuples,
        max_cochain_dim,
        max_matrix_entries,
        max_work_units,
    };
    Ok(InvariantLimits {
        hochschild_degree,
        bar,
    })
}

fn discovery_limits(c: &mut Cursor) -> Parse<DiscoveryLimits> {
    c.token(b'{')?;
    let [
        max_vertices,
        max_directed_mutations,
        max_total_terms,
        max_matrix_entries,
        max_hom_spaces,
    ] = c.uint_fields("$.limits.discovery", DISCOVERY_KEYS)?;
    let through_silting = c.next("through_silting", |c| c.bool())?;
    c.token(b'}')?;
    Ok(DiscoveryLimits {
        max_vertices,
        max_directed_mutations,
        max_total_terms,
        max_matrix_entries,
        tilting: TiltingComplexLimits { max_hom_spaces },
        through_silting,
    })
}

fn target_limits(c: &mut Cursor) -> Parse<TargetLimits> {
    let [
        endo,
        radical,
        paths,
        terms,
        basis,
        word,
        steps,
        origin,
        ambiguities,
    ] = c.uint_object("$.limits.target", TARGET_KEYS)?;
    Ok(TargetLimits {
        max_endo_dimension: endo,
        max_radical_products: radical,
        max_paths: paths,
        max_relation_terms: terms,
        completion: CompletionLimits {
            max_basis: basis,
            max_word_len: word,
            max_steps: steps,
            max_origin_terms: origin,
            max_ambiguities: ambiguities,
        },
    })
}

fn family(c: &mut Cursor, limits: &DerivedAtlasParseLimits) -> Parse<Family> {
    let members = c.next("members", |c| {
        c.array("$.members", limits.max_members, |c, member| {
            let text = c.escaped_string("$.members[]", limits.max_certificate_bytes)?;
            Certificate::from_json(&text)
                .map_err(|error| DerivedAtlasError::Certificate { member, error })
        })
    })?;
    let invariants = c.next("invariants", |c| {
        c.array("$.invariants", limits.max_members, |c, _| {
            readings(c, limits.max_entries)
        })
    })?;
    Ok(Family {
        members,
        invariants,
    })
}

fn readings(c: &mut Cursor, max_entries: usize) -> Parse<Vec<AtlasReading>> {
    let count = KIND_NAMES.len();
    let path = "$.invariants[]";
    let readings = c.array(path, count, |c, index| reading(c, index, max_entries))?;
    if readings.len() != count {
        return Err(c
            .syntax(format!("{path} must hold {count} readings"))
            .into());
    }
    Ok(readings)
}

fn reading(c: &mut Cursor, index: usize, max_entries: usize) -> Parse<AtlasReading> {
    c.token(b'{')?;
    c.key("kind")?;
    if c.string("$.invariants[][].kind")? != KIND_NAMES[index] {
        let message = format!("expected invariant kind {}", KIND_NAMES[index]);
        return Err(c.syntax(message).into());
    }
    let name = c.next("reading", |c| c.string("$.invariants[][].reading"))?;
    let reading = reading_body(c, &name, max_entries)?;
    c.token(b'}')?;
    Ok(reading)
}

/// The members after `reading` for the reading named `name`.
fn reading_body(c: &mut Cursor, name: &str, max_entries: usize) -> Parse<AtlasReading> {
    Ok(match name {
        "finished" => AtlasReading::Finished(c.next("value", |c| integers(c, max_entries))?),
        "stopped" => AtlasReading::Stopped(c.next("stop", stop)?),
        "not_applicable" => AtlasReading::NotApplicable,
        _ => return Err(c.syntax("unknown invariant reading").into()),
    })
}

fn stop(c: &mut Cursor) -> Result<AtlasStop, PortableError> {
    let name = c.string("$.invariants[][].stop")?;
    let stops = [AtlasStop::Overflow, AtlasStop::BarCut];
    let stop = stops.into_iter().find(|&stop| stop_name(stop) == name);
    stop.ok_or_else(|| c.syntax("unknown invariant stop"))
}

fn integers(c: &mut Cursor, max_entries: usize) -> Result<Vec<i128>, PortableError> {
    c.array("$.value", max_entries, |c, _| c.i128("$.value"))
}

fn pair(c: &mut Cursor, path: &str) -> Result<(usize, usize), PortableError> {
    c.token(b'[')?;
    let left = c.usize(path)?;
    c.token(b',')?;
    let right = c.usize(path)?;
    c.token(b']')?;
    Ok((left, right))
}

fn settlement(c: &mut Cursor, limits: &DerivedAtlasParseLimits) -> Parse<Settlement> {
    let entries = limits.max_entries;
    let classes = c.next("classes", |c| {
        c.array("$.classes", limits.max_members, |c, _| class(c, entries))
    })?;
    let separations = c.next("separations", |c| {
        c.array("$.separations", entries, |c, _| separation(c, entries))
    })?;
    let unresolved = c.next("unresolved", |c| {
        c.array("$.unresolved", entries, |c, _| unresolved(c, entries))
    })?;
    let walks = c.next("walks", |c| c.array("$.walks", entries, |c, _| walk(c)))?;
    Ok(Settlement {
        classes,
        separations,
        unresolved,
        walks,
    })
}

fn class(c: &mut Cursor, entries: usize) -> Parse<AtlasClass> {
    c.token(b'{')?;
    c.key("members")?;
    let members = c.numbers("$.classes[].members", entries)?;
    let merges = c.next("merges", |c| {
        c.array("$.classes[].merges", entries, |c, _| merge(c, entries))
    })?;
    c.token(b'}')?;
    Ok(AtlasClass { members, merges })
}

fn merge(c: &mut Cursor, entries: usize) -> Parse<AtlasMerge> {
    let path = "$.classes[].merges[]";
    c.token(b'{')?;
    c.key("source")?;
    let source = c.usize(path)?;
    let member = c.next("member", |c| c.usize(path))?;
    let recipe = c.next("recipe", |c| {
        c.array(path, entries, |c, _| {
            read_mutation(c, "$.classes[].merges[].recipe[]")
        })
    })?;
    let vertex_map = c.next("vertex_map", |c| {
        c.array(path, entries, |c, _| {
            let vertex = c.usize(path)?;
            u32::try_from(vertex).map_err(|_| c.syntax("vertex exceeds u32"))
        })
    })?;
    let arrow_images = c.next("arrow_images", |c| {
        c.array(path, entries, |c, _| {
            c.array(path, entries, |c, _| c.u64(path))
        })
    })?;
    c.token(b'}')?;
    Ok(AtlasMerge {
        source,
        member,
        recipe,
        vertex_map,
        arrow_images,
    })
}

fn separation(c: &mut Cursor, entries: usize) -> Parse<AtlasSeparation> {
    let path = "$.separations[]";
    c.token(b'{')?;
    c.key("classes")?;
    let classes = pair(c, path)?;
    let members = c.next("members", |c| pair(c, path))?;
    let name = c.next("kind", |c| c.string(path))?;
    let kind = kind_from_name(&name).ok_or_else(|| c.syntax("unknown invariant kind"))?;
    let left = c.next("left", |c| integers(c, entries))?;
    let right = c.next("right", |c| integers(c, entries))?;
    c.token(b'}')?;
    Ok(AtlasSeparation {
        classes,
        members,
        kind,
        left,
        right,
    })
}

fn unresolved(c: &mut Cursor, entries: usize) -> Parse<UnresolvedPair> {
    c.token(b'{')?;
    c.key("classes")?;
    let classes = pair(c, "$.unresolved[].classes")?;
    let walks = c.next("walks", |c| c.numbers("$.unresolved[].walks", entries))?;
    c.token(b'}')?;
    Ok(UnresolvedPair { classes, walks })
}

fn walk(c: &mut Cursor) -> Parse<MutationWalk> {
    let path = "$.walks[]";
    c.token(b'{')?;
    c.key("member")?;
    let member = c.usize(path)?;
    let stop = c.next("stop", discovery_stop)?;
    c.token(b',')?;
    let [vertices, blocked, examined, target_cuts, unmatched, merges] =
        c.uint_fields(path, WALK_KEYS)?;
    c.token(b'}')?;
    Ok(MutationWalk {
        member,
        stop,
        vertices,
        blocked,
        examined,
        target_cuts,
        unmatched,
        merges,
    })
}

fn discovery_stop(c: &mut Cursor) -> Parse<DiscoveryStop> {
    c.token(b'{')?;
    c.key("kind")?;
    let name = c.string("$.walks[].stop.kind")?;
    let keys = stop_keys(&name).ok_or_else(|| c.syntax("unknown discovery stop"))?;
    let values = keys
        .iter()
        .map(|key| c.next(key, |c| c.u64("$.walks[].stop")))
        .collect::<Result<Vec<_>, PortableError>>()?;
    c.token(b'}')?;
    Ok(stop_from(&name, &values))
}

fn status(c: &mut Cursor) -> Result<ClassificationStatus, PortableError> {
    let name = c.string("$.status")?;
    let statuses = [
        ClassificationStatus::Complete,
        ClassificationStatus::Incomplete,
    ];
    let status = statuses.into_iter().find(|status| status.as_str() == name);
    status.ok_or_else(|| c.syntax("status must be complete or incomplete"))
}
