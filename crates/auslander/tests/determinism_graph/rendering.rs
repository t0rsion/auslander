use std::fmt::Write as _;

use auslander::mutation::ExchangeShape;
use auslander::taugraph::{ClosedSupportTauTiltingGraph, SlotRecord};

use super::payload::{digest, endpoint_digest, mutation_digest};

/// `dims` joined by commas, or `-` when it is empty.
fn joined(dims: &[usize]) -> String {
    if dims.is_empty() {
        return "-".to_string();
    }
    dims.iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(",")
}

fn vertex_dims(summands: &[Vec<usize>]) -> String {
    if summands.is_empty() {
        return "-".to_string();
    }
    summands
        .iter()
        .map(|dims| joined(dims))
        .collect::<Vec<_>>()
        .join("|")
}

fn support(vertices: &[u32]) -> String {
    if vertices.is_empty() {
        return "-".to_string();
    }
    vertices
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join(",")
}

fn slot_records(records: &[SlotRecord]) -> String {
    if records.is_empty() {
        return "-".to_string();
    }
    records
        .iter()
        .map(|record| match record {
            SlotRecord::LeftMutation { mutation } => format!("e{mutation}"),
            SlotRecord::NoLeftMutation(witness) => format!(
                "f{}:{}",
                witness.maps().len(),
                digest(|p| p.fac("fac", witness))
            ),
        })
        .collect::<Vec<_>>()
        .join(",")
}

fn shape(shape: &ExchangeShape) -> String {
    match shape {
        ExchangeShape::MovesToProjective { vertex } => format!("proj:{vertex}"),
        ExchangeShape::ReplacedByModule { multiplicity } => format!("module:{multiplicity}"),
    }
}

fn bijection(bijection: &[usize]) -> String {
    if bijection.is_empty() {
        return "-".to_string();
    }
    bijection
        .iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(",")
}

/// The normalized rendering of `graph`, in the format the module doc states.
pub(crate) fn normalized_rendering(graph: &ClosedSupportTauTiltingGraph) -> String {
    let mut out = String::new();
    writeln!(out, "units={}", graph.work_units()).unwrap();
    for (index, vertex) in graph.vertices().iter().enumerate() {
        writeln!(
            out,
            "v{index} dim={} proj={} slots={} mod={} tau={}",
            vertex_dims(&vertex.pair().module().dim_vectors()),
            support(vertex.pair().projective().vertices()),
            slot_records(vertex.slots()),
            digest(|p| p.decomposition("pair_module", vertex.pair().module())),
            digest(|p| p.rigid("pair_rigid", vertex.pair().rigid())),
        )
        .unwrap();
    }
    for (index, edge) in graph.mutations().iter().enumerate() {
        let witness = edge.mutation().witness();
        let endpoint = edge.endpoint();
        writeln!(
            out,
            "e{index} {}:{}->{} shape={} exchanged={} target={} bij={} seq={} iso={} mut={} \
             acp={} add={} approx={}",
            edge.source(),
            edge.slot(),
            edge.target(),
            shape(edge.mutation().shape()),
            joined(witness.exchanged().dim_vector()),
            joined(witness.target_module().dim_vector()),
            bijection(endpoint.bijection()),
            digest(|p| {
                p.morphism("approximation", witness.approximation().map());
                p.morphism("exchange", witness.exchange());
            }),
            endpoint_digest(
                endpoint.bijection(),
                endpoint.forward(),
                endpoint.backward()
            ),
            mutation_digest(edge.mutation()),
            digest(|p| p.almost_complete("almost_complete", witness.almost_complete())),
            digest(|p| {
                p.add_closure("source_extension", witness.source_extension());
                p.add_closure("target_extension", witness.target_extension());
            }),
            digest(|p| p.approximation("approximation", witness.approximation())),
        )
        .unwrap();
    }
    out
}
