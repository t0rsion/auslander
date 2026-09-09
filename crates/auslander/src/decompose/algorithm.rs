use crate::endo::{EndoAlgebra, SplitMix64};
use crate::field::Fp;
use crate::hom::{Morphism, identity, submodule_with_inclusion};
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::profile::{Site, hit_module};

use super::outcome::{Certificate, Decomposition};
use super::split::Split;

const FITTING_ATTEMPTS: u32 = 64;
pub(crate) const DECOMPOSE_SEED: u64 = 0x000a_0512_a11d_e12b;

/// Splits `m` into summands with certificates; the zero module decomposes into
/// no summands. Deterministic: all randomness is seeded per call.
pub fn decompose(m: &Module) -> Decomposition {
    let root = (!m.is_zero()).then(|| EndoAlgebra::new(m));
    decompose_with_root_endo(m, root)
}

pub(crate) fn decompose_with_root_endo(m: &Module, root: Option<EndoAlgebra>) -> Decomposition {
    hit_module(Site::Decompose, m);
    let mut rng = SplitMix64(DECOMPOSE_SEED);
    let mut parts = Vec::new();
    if let Some(endo) = root {
        split_recursively(m, endo, identity(m), identity(m), &mut rng, &mut parts);
    }
    let mut summands = Vec::with_capacity(parts.len());
    let mut inclusions = Vec::with_capacity(parts.len());
    let mut projections = Vec::with_capacity(parts.len());
    let mut certificates = Vec::with_capacity(parts.len());
    let mut endos = Vec::with_capacity(parts.len());
    for part in parts {
        summands.push(part.summand);
        inclusions.push(part.include);
        projections.push(part.project);
        certificates.push(part.certificate);
        endos.push(part.endo);
    }
    let split = Split::new(m, summands, inclusions, projections)
        .expect("recursive splits compose to a verified split");
    Decomposition::from_parts(split, certificates, endos)
}

struct Part {
    summand: Module,
    endo: EndoAlgebra,
    include: Morphism,
    project: Morphism,
    certificate: Certificate,
}

// `include: m → total`, `project: total → m` accumulate the position of `m`
// inside the original module across the recursion. `endo` is `End(m)`: the root
// builds it, and each part inherits its radical from the endomorphism algebra
// of the node it was split off, which is what makes one decomposition cost one
// radical chain instead of one per node.
fn split_recursively(
    m: &Module,
    endo: EndoAlgebra,
    include: Morphism,
    project: Morphism,
    rng: &mut SplitMix64,
    out: &mut Vec<Part>,
) {
    if endo.is_local() {
        finish_part(m, endo, include, project, Certificate::Indecomposable, out);
        return;
    }
    let split = deterministic_split(m, &endo, rng)
        .or_else(|| singular_split(m, &endo, rng))
        .or_else(|| fitting_split(m, &endo, rng));
    let Some(split) = split else {
        finish_part(
            m,
            endo,
            include,
            project,
            Certificate::Undetermined {
                attempts: FITTING_ATTEMPTS,
            },
            out,
        );
        return;
    };
    for k in 0..split.summands().len() {
        let summand = &split.summands()[k];
        if summand.is_zero() {
            continue;
        }
        let summand_endo = EndoAlgebra::from_summand(
            summand,
            &endo,
            &split.inclusions()[k],
            &split.projections()[k],
        );
        let summand_include = split.inclusions()[k]
            .then(&include)
            .expect("inclusion chains compose");
        let summand_project = project
            .then(&split.projections()[k])
            .expect("projection chains compose");
        split_recursively(
            summand,
            summand_endo,
            summand_include,
            summand_project,
            rng,
            out,
        );
    }
}

fn finish_part(
    m: &Module,
    endo: EndoAlgebra,
    include: Morphism,
    project: Morphism,
    certificate: Certificate,
    out: &mut Vec<Part>,
) {
    out.push(Part {
        summand: m.clone(),
        endo,
        include,
        project,
        certificate,
    });
}

// M = im(e) ⊕ im(1 − e) for a lifted idempotent e of End(M).
pub(crate) fn deterministic_split(
    m: &Module,
    endo: &EndoAlgebra,
    rng: &mut SplitMix64,
) -> Option<Split> {
    let e = endo.morphism(&endo.split_idempotent(rng)?);
    let field = m.field();
    let n = m.algebra().quiver().num_vertices();
    let mut first = Vec::with_capacity(n as usize);
    let mut second = Vec::with_capacity(n as usize);
    for v in 0..n {
        let ev = e.map_at(v);
        let mut complement = DenseMat::identity(ev.rows());
        complement.add_scaled_assign(ev, field.neg(field.one()), &field);
        first.push(ev.row_space_basis(&field));
        second.push(complement.row_space_basis(&field));
    }
    split_from_bases(m, first, second)
}

// M = ker(φⁿ) ⊕ im(φⁿ) for a φ that is neither invertible nor nilpotent,
// which is what makes both parts nonzero. Such a φ is constructed rather than
// drawn: see EndoAlgebra::singular_element for why sampling does not find one.
fn singular_split(m: &Module, endo: &EndoAlgebra, rng: &mut SplitMix64) -> Option<Split> {
    let coords = endo.singular_element(rng, FITTING_ATTEMPTS)?;
    fitting_split_along(m, &endo.morphism(&coords))
}

// M = ker(φⁿ) ⊕ im(φⁿ), n = dim_k M, for seeded-random φ; both parts are
// nonzero exactly when the image of φ in End/rad is a nonzero non-unit.
fn fitting_split(m: &Module, endo: &EndoAlgebra, rng: &mut SplitMix64) -> Option<Split> {
    let field = m.field();
    let p = field.modulus();
    for _ in 0..FITTING_ATTEMPTS {
        let coords: Vec<Fp> = (0..endo.dim())
            .map(|_| field.elem(rng.below(p) as i64))
            .collect();
        if let Some(split) = fitting_split_along(m, &endo.morphism(&coords)) {
            return Some(split);
        }
    }
    None
}

// The Fitting decomposition along one endomorphism, n = dim_k M. None when the
// split would be trivial: φⁿ injective leaves no kernel, φⁿ zero leaves no image.
fn fitting_split_along(m: &Module, phi: &Morphism) -> Option<Split> {
    let field = m.field();
    let psi = morphism_power(m, phi, m.total_dim());
    let n = m.algebra().quiver().num_vertices();
    let mut kernel = Vec::with_capacity(n as usize);
    let mut image = Vec::with_capacity(n as usize);
    for v in 0..n {
        kernel.push(psi.map_at(v).left_kernel_basis(&field));
        image.push(psi.map_at(v).row_space_basis(&field));
    }
    if kernel.iter().all(|b| b.rows() == 0) || image.iter().all(|b| b.rows() == 0) {
        return None;
    }
    split_from_bases(m, kernel, image)
}

fn morphism_power(m: &Module, phi: &Morphism, exp: usize) -> Morphism {
    binary_power!(phi.clone(), identity(m), exp, |left, right| left
        .then(right)
        .expect("endomorphisms compose"))
}

/// A verified two-summand split from per-vertex row bases of two invariant
/// subspace families, or `None` when they are not complementary.
///
/// Both families must be A-invariant. All three routes into this function pass
/// the image or the kernel of an endomorphism of `m`, so both are submodules.
/// [`submodule_with_inclusion`] would panic on a family that is not.
///
/// The two projections are built with [`Morphism::new_unchecked`]. The loop below
/// returns `None` unless the stacked bases at each vertex are square and
/// invertible, so at that point `M_v` is the vector-space direct sum of the two
/// row spaces `U_v` and `W_v`, and `x · proj_first[v]` reads off the coordinates
/// of the `U_v` part of `x` over `first[v]`. With `U` and `W` both submodules,
/// that projection is A-linear: write `x = u + w` at `s(a)`, then
/// `x M(a) = u M(a) + w M(a)` with `u M(a)` in `U_{t(a)}` and `w M(a)` in
/// `W_{t(a)}`, so projecting after acting and acting after projecting give the
/// same element. In matrices that is the square
/// `proj_first[s(a)] · S(a) = M(a) · proj_first[t(a)]` for the induced `S(a)` of
/// the submodule. The shapes are right because `proj_first[v]` is
/// `dim M_v x k1` and `k1` is `sub1.dim_at(v)`, and the entries come from
/// [`DenseMat::inverse`] over the module's own field. That argument is not
/// the certificate: [`Split::new`] still rechecks every split identity on the
/// returned maps, and this returns `None` if one fails.
fn split_from_bases(m: &Module, first: Vec<DenseMat>, second: Vec<DenseMat>) -> Option<Split> {
    let field = m.field();
    let n = m.algebra().quiver().num_vertices() as usize;
    let mut proj_first = Vec::with_capacity(n);
    let mut proj_second = Vec::with_capacity(n);
    for v in 0..n {
        let k1 = first[v].rows();
        let k2 = second[v].rows();
        if k1 + k2 != m.dim_vector()[v] {
            return None;
        }
        let stacked = DenseMat::stack(&[&first[v], &second[v]], m.dim_vector()[v]);
        // The two row counts add up to the vertex dimension, checked above,
        // so the stack is square.
        let inverse = stacked.inverse(&field)?;
        let mut p1 = DenseMat::zero(inverse.rows(), k1);
        let mut p2 = DenseMat::zero(inverse.rows(), k2);
        for r in 0..inverse.rows() {
            for c in 0..k1 {
                p1.set(r, c, inverse.get(r, c));
            }
            for c in 0..k2 {
                p2.set(r, c, inverse.get(r, k1 + c));
            }
        }
        proj_first.push(p1);
        proj_second.push(p2);
    }
    let (sub1, incl1) = submodule_with_inclusion(m, first);
    let (sub2, incl2) = submodule_with_inclusion(m, second);
    let proj1 = Morphism::new_unchecked(m, &sub1, proj_first);
    let proj2 = Morphism::new_unchecked(m, &sub2, proj_second);
    Split::new(m, vec![sub1, sub2], vec![incl1, incl2], vec![proj1, proj2]).ok()
}
