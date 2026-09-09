use std::sync::Arc;

use super::*;
use crate::algebra::Algebra;
use crate::algebra::{
    commutative_square, kronecker, linear_an, linear_nakayama, radical_square_zero_cycle,
    truncated_poly,
};
use crate::ar::tau;
use crate::arquiver::{CatalogProvenance, IndecomposableCatalog};
use crate::basic::{BasicDecomposition, ProjectiveSupport};
use crate::dynkin::{DynkinError, DynkinType, dynkin_quiver};
use crate::enumerate::EnumerateError;
use crate::field::PrimeField;
use crate::hom::hom_dim;
use crate::iso::{IsoOutcome, is_isomorphic};
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::quiver::Quiver;
use crate::taurigid::TauCache;

fn f2() -> PrimeField {
    PrimeField::new(2).unwrap()
}

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

fn fields() -> [PrimeField; 2] {
    [f2(), f5()]
}

fn path_algebra(quiver: Quiver, field: PrimeField) -> Arc<Algebra> {
    crate::algebra::path_algebra(quiver, field)
        .expect("the zero ideal over an acyclic quiver completes")
}

// D_4 as dynkin_quiver builds it: vertex 0 is the center, arrows 0 -> 1,
// 0 -> 2, 0 -> 3.
fn d4(field: PrimeField) -> Arc<Algebra> {
    path_algebra(
        dynkin_quiver(DynkinType::D(4)).expect("D_4 has a quiver"),
        field,
    )
}

// The semisimple algebra on n vertices: n vertices, no arrows. Every
// vertex has no incoming and no outgoing arrow, so the quiver is Nakayama
// and the catalog is the n simples.
fn semisimple(n: u32, field: PrimeField) -> Arc<Algebra> {
    path_algebra(
        Quiver::new(n, &[]).expect("no arrow is out of range"),
        field,
    )
}

fn basic(m: &Module) -> BasicDecomposition {
    BasicDecomposition::new(m).expect("the fixture module is basic")
}

fn support(algebra: &Arc<Algebra>, vertices: &[u32]) -> ProjectiveSupport {
    ProjectiveSupport::new(algebra, vertices).expect("the fixture vertices are in range")
}

fn all_vertices(algebra: &Arc<Algebra>) -> Vec<u32> {
    (0..algebra.quiver().num_vertices()).collect()
}

/// The regular module `A = P_0 + ... + P_{n-1}`, basic over a basic
/// algebra.
fn regular(algebra: &Arc<Algebra>) -> Module {
    let parts: Vec<Module> = all_vertices(algebra)
        .iter()
        .map(|&v| Module::projective(algebra, v))
        .collect();
    let refs: Vec<&Module> = parts.iter().collect();
    sum(algebra, &refs)
}

/// The direct sum of `parts`, and the zero module when `parts` is empty.
/// Production code builds its decompositions from the catalog instead.
fn sum(algebra: &Arc<Algebra>, parts: &[&Module]) -> Module {
    if parts.is_empty() {
        Module::zero(algebra)
    } else {
        crate::module::direct_sum(parts).0
    }
}

fn expect_pair(classification: SupportTauTiltingClassification) -> SupportTauTiltingPair {
    match classification {
        SupportTauTiltingClassification::Pair(pair) => pair,
        SupportTauTiltingClassification::Rejected(rejection) => {
            panic!(
                "expected a pair, got condition {} : {rejection}",
                rejection.condition()
            )
        }
    }
}

fn expect_rejection(classification: SupportTauTiltingClassification) -> PairRejection {
    match classification {
        SupportTauTiltingClassification::Rejected(rejection) => rejection,
        SupportTauTiltingClassification::Pair(pair) => {
            panic!("expected a rejection, got {pair:?}")
        }
    }
}

/// The fixture algebras that carry an exhaustive catalog, named for
/// failure messages.
fn catalog_fixtures(field: PrimeField) -> Vec<(String, IndecomposableCatalog)> {
    let modulus = field.modulus();
    let mut out = Vec::new();
    for n in [2u32, 3, 4] {
        let algebra = semisimple(n, field);
        out.push((
            format!("semisimple({n}) over F_{modulus}"),
            IndecomposableCatalog::nakayama(&algebra).expect("no arrow means Nakayama"),
        ));
    }
    for n in [2usize, 3] {
        let algebra = linear_an(n, field);
        out.push((
            format!("linear_an({n}) over F_{modulus}"),
            IndecomposableCatalog::dynkin(&algebra).expect("A_n is Dynkin"),
        ));
    }
    let tp = truncated_poly(3, field).expect("k[x]/(x^3) is admissible");
    out.push((
        format!("truncated_poly(3) over F_{modulus}"),
        IndecomposableCatalog::nakayama(&tp).expect("one loop is Nakayama"),
    ));
    let cycle = radical_square_zero_cycle(3, field);
    out.push((
        format!("radical_square_zero_cycle(3) over F_{modulus}"),
        IndecomposableCatalog::nakayama(&cycle).expect("a cycle is Nakayama"),
    ));
    let nakayama = linear_nakayama(&[2, 2, 1], field).expect("[2, 2, 1] is a Kupisch series");
    out.push((
        format!("linear_nakayama([2, 2, 1]) over F_{modulus}"),
        IndecomposableCatalog::nakayama(&nakayama).expect("a linear quiver is Nakayama"),
    ));
    out
}

/// An independent count of the pairs, by brute force over every subset of
/// the catalog and every vertex subset.
///
/// Nothing here is shared with [`enumerate_over_catalog`]: `tau` runs
/// uncached through the double route, the supports come from dimension
/// vectors rather than from a Hom table, and the subsets are enumerated by
/// bitmask with no pruning at all. It returns the pair count, the
/// histogram by `|M|`, and the number of tau-rigid subsets of at most `n`
/// entries, which is what the walk counts as nodes.
fn brute_force(catalog: &IndecomposableCatalog) -> (usize, Vec<usize>, usize) {
    let algebra = catalog.algebra();
    let vertices = algebra.quiver().num_vertices() as usize;
    let k = catalog.len();
    assert!(k < 20, "the bitmask walk needs a small catalog");
    let translates: Vec<Module> = catalog
        .entries()
        .iter()
        .map(|x| tau(x.module()).expect("the fixture translates"))
        .collect();
    let mut tau_hom = vec![vec![0usize; k]; k];
    for (i, x) in catalog.entries().iter().enumerate() {
        for (j, translate) in translates.iter().enumerate() {
            if !translate.is_zero() {
                tau_hom[i][j] = hom_dim(x.module(), translate).expect("one algebra");
            }
        }
    }
    let mut pairs = 0;
    let mut histogram = vec![0usize; vertices + 1];
    let mut nodes = 0;
    for mask in 0..(1u32 << k) {
        let chosen: Vec<usize> = (0..k).filter(|&i| mask & (1 << i) != 0).collect();
        let rigid = chosen
            .iter()
            .all(|&i| chosen.iter().all(|&j| tau_hom[i][j] == 0));
        if !rigid {
            continue;
        }
        if chosen.len() <= vertices {
            nodes += 1;
        }
        if chosen.len() > vertices {
            continue;
        }
        // Hom(P_v, M) is zero exactly when M vanishes at v.
        let zero_support = (0..vertices)
            .filter(|&v| {
                chosen
                    .iter()
                    .all(|&i| catalog.entries()[i].module().dim_vector()[v] == 0)
            })
            .count();
        let want = vertices - chosen.len();
        if zero_support < want {
            continue;
        }
        let choices = (0..want).fold(1usize, |acc, t| acc * (zero_support - t) / (t + 1));
        pairs += choices;
        histogram[chosen.len()] += choices;
    }
    (pairs, histogram, nodes)
}

mod almost_tests;
mod enumeration_tests;
mod pair_tests;
mod residue_tests;
mod verification_tests;
