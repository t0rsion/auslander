use auslander::algebra::truncated_poly;
use auslander::ext::{ExtClass, ExtSpace, ext_dim};
use auslander::field::Fp;
use auslander::hom::hom_dim;
use auslander::module::Module;
use auslander::radical::radical;
use auslander::sequence::{ShortExactSequence, SplitStatus};

use crate::common::{basis_class, f2, f5};

use super::support::{
    MAX_DEGREE, SimpleExt, add_morphisms, coboundaries, tier1_ext, tier1_fixtures,
};

#[test]
fn ext_space_dims_match_ext_dim_between_all_simples_and_hom_dim_at_degree_0() {
    for (name, algebra) in tier1_fixtures() {
        let n = algebra.quiver().num_vertices();
        let simples: Vec<Module> = (0..n).map(|v| Module::simple(&algebra, v)).collect();
        for (i, si) in simples.iter().enumerate() {
            for (j, sj) in simples.iter().enumerate() {
                for k in 0..=MAX_DEGREE {
                    let space = ExtSpace::new(si, sj, k).unwrap();
                    assert_eq!(
                        space.dim(),
                        ext_dim(si, sj, k).unwrap(),
                        "{name}: Ext^{k}(S_{i}, S_{j})"
                    );
                    if k == 0 {
                        assert_eq!(
                            space.dim(),
                            hom_dim(si, sj).unwrap(),
                            "{name}: Ext^0(S_{i}, S_{j}) vs Hom"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn identity_classes_are_two_sided_units_on_every_nonzero_bounded_space() {
    for (name, _, ext) in tier1_ext() {
        let n = ext.simples.len();
        for i in 0..n {
            for j in 0..n {
                for k in 0..=MAX_DEGREE {
                    if ext.dims[i][j][k] == 0 {
                        continue;
                    }
                    let id_left = ext.space(i, i, 0).identity_class().unwrap();
                    let id_right = ext.space(j, j, 0).identity_class().unwrap();
                    for (b, alpha) in ext.basis(i, j, k).iter().enumerate() {
                        assert!(
                            id_left.then(alpha).unwrap().equals(alpha).unwrap(),
                            "{name}: left unit on Ext^{k}(S_{i}, S_{j}) basis {b}"
                        );
                        assert!(
                            alpha.then(&id_right).unwrap().equals(alpha).unwrap(),
                            "{name}: right unit on Ext^{k}(S_{i}, S_{j}) basis {b}"
                        );
                    }
                }
            }
        }
    }
}

fn assert_scaled_products(u: &ExtClass, v: &ExtClass, two: Fp, at: &str, target_dim: usize) {
    let product = u.then(v).unwrap();
    assert_eq!(
        product.space().dim(),
        target_dim,
        "{at}: product space dimension"
    );
    assert!(
        u.scale(two)
            .then(v)
            .unwrap()
            .equals(&product.scale(two))
            .unwrap(),
        "{at}: left scaling"
    );
    assert!(
        u.then(&v.scale(two))
            .unwrap()
            .equals(&product.scale(two))
            .unwrap(),
        "{at}: right scaling"
    );
    assert!(
        u.neg().then(v).unwrap().equals(&product.neg()).unwrap(),
        "{at}: negation"
    );
}

fn assert_left_additivity(left: &[ExtClass], right: &[ExtClass], at: &str) {
    for first in left {
        for second in left {
            for value in right {
                let sum_product = first.add(second).unwrap().then(value).unwrap();
                let product_sum = first
                    .then(value)
                    .unwrap()
                    .add(&second.then(value).unwrap())
                    .unwrap();
                assert!(
                    sum_product.equals(&product_sum).unwrap(),
                    "{at}: left additivity"
                );
            }
        }
    }
}

fn assert_right_additivity(left: &[ExtClass], right: &[ExtClass], at: &str) {
    for value in left {
        for first in right {
            for second in right {
                let product_sum = value.then(&first.add(second).unwrap()).unwrap();
                let sum_product = value
                    .then(first)
                    .unwrap()
                    .add(&value.then(second).unwrap())
                    .unwrap();
                assert!(
                    product_sum.equals(&sum_product).unwrap(),
                    "{at}: right additivity"
                );
            }
        }
    }
}

fn assert_bilinear_basis_pair(
    left: &[ExtClass],
    right: &[ExtClass],
    two: Fp,
    target_dim: usize,
    at: &str,
) -> usize {
    for first in left {
        for second in right {
            assert_scaled_products(first, second, two, at, target_dim);
        }
    }
    assert_left_additivity(left, right, at);
    assert_right_additivity(left, right, at);
    let left_zero = left[0].space().zero_class();
    let right_zero = right[0].space().zero_class();
    assert!(
        left_zero.then(&right[0]).unwrap().is_zero(),
        "{at}: left zero"
    );
    assert!(
        left[0].then(&right_zero).unwrap().is_zero(),
        "{at}: right zero"
    );
    left.len() * right.len()
}

#[test]
fn yoneda_products_are_bilinear_on_every_bounded_basis_pair() {
    for (name, _, ext) in tier1_ext() {
        let field = ext.simples[0].field();
        let two = field.elem(2);
        let n = ext.simples.len();
        let mut checked = 0usize;
        for i in 0..n {
            for j in 0..n {
                for l in 0..n {
                    for m in 0..=MAX_DEGREE {
                        for d in 0..=(MAX_DEGREE - m) {
                            if ext.dims[i][j][m] == 0 || ext.dims[j][l][d] == 0 {
                                continue;
                            }
                            let a_basis = ext.basis(i, j, m);
                            let b_basis = ext.basis(j, l, d);
                            let at =
                                format!("{name}: Ext^{m}(S_{i}, S_{j}) x Ext^{d}(S_{j}, S_{l})");
                            checked += assert_bilinear_basis_pair(
                                &a_basis,
                                &b_basis,
                                two,
                                ext.dims[i][l][m + d],
                                &at,
                            );
                        }
                    }
                }
            }
        }
        assert!(
            checked > 0,
            "{name}: the bounded range contains composable nonzero pairs"
        );
    }
}

fn assert_associative_basis(
    left: &[ExtClass],
    middle: &[ExtClass],
    right: &[ExtClass],
    message: &str,
) -> usize {
    let mut checked = 0;
    for first in left {
        for second in middle {
            for third in right {
                let left_product = first.then(second).unwrap().then(third).unwrap();
                let right_product = first.then(&second.then(third).unwrap()).unwrap();
                assert!(left_product.equals(&right_product).unwrap(), "{message}");
                checked += 1;
            }
        }
    }
    checked
}

fn assert_associativity_at_vertices(
    name: &str,
    ext: &SimpleExt,
    source: usize,
    first_middle: usize,
    second_middle: usize,
    target: usize,
) -> usize {
    let mut checked = 0;
    for first_degree in 0..=MAX_DEGREE {
        for second_degree in 0..=(MAX_DEGREE - first_degree) {
            for third_degree in 0..=(MAX_DEGREE - first_degree - second_degree) {
                if ext.dims[source][first_middle][first_degree] == 0
                    || ext.dims[first_middle][second_middle][second_degree] == 0
                    || ext.dims[second_middle][target][third_degree] == 0
                {
                    continue;
                }
                let message = format!(
                    "{name}: associativity on degrees ({first_degree}, {second_degree}, \
                     {third_degree}) at (S_{source}, S_{first_middle}, S_{second_middle}, \
                     S_{target})"
                );
                checked += assert_associative_basis(
                    &ext.basis(source, first_middle, first_degree),
                    &ext.basis(first_middle, second_middle, second_degree),
                    &ext.basis(second_middle, target, third_degree),
                    &message,
                );
            }
        }
    }
    checked
}

#[test]
fn yoneda_products_are_associative_on_every_bounded_basis_triple() {
    for (name, _, ext) in tier1_ext() {
        let n = ext.simples.len();
        let mut checked = 0usize;
        for i in 0..n {
            for j in 0..n {
                for l in 0..n {
                    for q in 0..n {
                        checked += assert_associativity_at_vertices(name, ext, i, j, l, q);
                    }
                }
            }
        }
        assert!(
            checked > 0,
            "{name}: the bounded range contains composable nonzero triples"
        );
    }
}

// Over A = k[x]/(x^3) with R = rad P = A/(x^2): the minimal resolution of
// S has d_1 = right multiplication by x and d_2 = right multiplication by
// x^2. Hom(P, R) has dimension 2, delta^0 sends f to f(1) x with image R x
// of dimension 1, and delta^1 sends f to f(1) x^2 = 0 in A/(x^2). So
// B^1(S, R) has dimension 1, Z^1 = Hom(P, R), and Ext^1(S, R) has
// dimension 1. Ext^1(R, S) also has dimension 1: the resolution of R
// swaps the two differentials and both compose to zero into S. The counts
// are characteristic free, so both fields run.
//
// This test works at the class level: it reduces the shifted cocycle to
// its class and multiplies the class, so the product construction only
// ever sees the canonical representative. The representative-level gate,
// which runs the lift construction on the altered cocycle itself, is the
// ext.rs unit test
// `a_left_cocycle_shifted_by_a_coboundary_lifts_to_the_same_product` (and
// its right-factor sibling).
#[test]
fn a_shifted_cocycle_recovers_its_class_and_the_class_product_is_unchanged() {
    for field in [f2(), f5()] {
        let algebra = truncated_poly(3, field).unwrap();
        let s = Module::simple(&algebra, 0);
        let r = radical(&Module::projective(&algebra, 0)).0;
        let left = ExtSpace::new(&s, &r, 1).unwrap();
        let right = ExtSpace::new(&r, &s, 1).unwrap();
        assert_eq!(left.dim(), 1, "Ext^1(S, R) over F_{}", field.modulus());
        assert_eq!(right.dim(), 1, "Ext^1(R, S) over F_{}", field.modulus());
        let alpha = basis_class(&left, 0);
        let beta = basis_class(&right, 0);
        let product = alpha.then(&beta).unwrap();
        let shifts = coboundaries(&left);
        assert!(
            !shifts.is_empty(),
            "B^1(S, R) is nonzero by the derivation above"
        );
        for b in &shifts {
            let shifted = add_morphisms(&alpha.representative(), b);
            let recovered = left.class_from_cocycle(&shifted).unwrap();
            assert!(
                recovered.equals(&alpha).unwrap(),
                "the shifted cocycle keeps its class over F_{}",
                field.modulus()
            );
            assert!(
                recovered.then(&beta).unwrap().equals(&product).unwrap(),
                "the shifted cocycle keeps its product over F_{}",
                field.modulus()
            );
        }
    }
}

// Class level only: recovery round-trips each factor through its
// extension and multiplies the recovered classes, which equal the
// original classes, so both products run the same construction. The
// gate that recovers the pre-reduction connecting cocycle from the
// extension object and splices it independently is the ext.rs unit test
// `the_cocycle_recovered_from_the_extension_splices_to_the_product`.
#[test]
fn ext1_class_recovery_round_trips_and_the_recovered_classes_compose_alike() {
    for (name, _, ext) in tier1_ext() {
        let n = ext.simples.len();
        let mut checked = 0usize;
        for i in 0..n {
            for j in 0..n {
                for l in 0..n {
                    if ext.dims[i][j][1] == 0 || ext.dims[j][l][1] == 0 {
                        continue;
                    }
                    let a_space = ext.space(i, j, 1);
                    let b_space = ext.space(j, l, 1);
                    for alpha in &ext.basis(i, j, 1) {
                        for beta in &ext.basis(j, l, 1) {
                            let ses_a = ShortExactSequence::from_ext1(alpha).unwrap();
                            let ses_b = ShortExactSequence::from_ext1(beta).unwrap();
                            let recovered_a = ses_a.ext1_class(a_space).unwrap();
                            let recovered_b = ses_b.ext1_class(b_space).unwrap();
                            assert!(recovered_a.equals(alpha).unwrap(), "{name}: left recovery");
                            assert!(recovered_b.equals(beta).unwrap(), "{name}: right recovery");
                            // The recovered classes equal the originals,
                            // so this checks that recovery feeds the
                            // product construction unchanged, not the
                            // splice itself; see the ext.rs gate above.
                            let direct = alpha.then(beta).unwrap();
                            let via_recovery = recovered_a.then(&recovered_b).unwrap();
                            assert!(
                                via_recovery.equals(&direct).unwrap(),
                                "{name}: recovered-class product at (S_{i}, S_{j}, S_{l})"
                            );
                            assert_eq!(
                                direct.space().dim(),
                                ext.dims[i][l][2],
                                "{name}: product dimension at (S_{i}, S_{l})"
                            );
                            checked += 1;
                        }
                    }
                }
            }
        }
        assert!(checked > 0, "{name}: some Ext^1 pair composes");
    }
}

fn assert_nonzero_ext1_round_trip(
    name: &str,
    vertices: u32,
    source: usize,
    target: usize,
    basis: usize,
    class: &ExtClass,
    space: &ExtSpace,
) {
    let sequence = ShortExactSequence::from_ext1(class).unwrap();
    assert!(
        sequence.quotient().ptr_eq(space.source()),
        "{name}: quotient"
    );
    assert!(sequence.sub().ptr_eq(space.target()), "{name}: sub");
    for vertex in 0..vertices {
        assert_eq!(
            sequence.middle().dim_at(vertex),
            sequence.sub().dim_at(vertex) + sequence.quotient().dim_at(vertex),
            "{name}: dimensions at vertex {vertex} for Ext^1(S_{source}, S_{target}) basis {basis}"
        );
    }
    let recovered = sequence.ext1_class(space).unwrap();
    assert!(
        recovered.equals(class).unwrap(),
        "{name}: round trip of Ext^1(S_{source}, S_{target}) basis {basis}"
    );
    match sequence.split_status() {
        SplitStatus::NonSplit(witness) => assert!(witness.verify(&sequence), "{name}: witness"),
        SplitStatus::Split(_) => panic!("{name}: the nonzero basis class {basis} split"),
    }
}

fn assert_zero_ext1_round_trip(name: &str, source: usize, target: usize, space: &ExtSpace) {
    let sequence = ShortExactSequence::from_ext1(&space.zero_class()).unwrap();
    assert!(
        sequence.ext1_class(space).unwrap().is_zero(),
        "{name}: the zero class recovers zero"
    );
    match sequence.split_status() {
        SplitStatus::Split(witness) => assert!(witness.verify(&sequence), "{name}: split witness"),
        SplitStatus::NonSplit(_) => {
            panic!("{name}: the zero class of Ext^1(S_{source}, S_{target}) did not split")
        }
    }
}

#[test]
fn from_ext1_round_trips_every_basis_class_and_split_status_matches_is_zero() {
    for (name, algebra, ext) in tier1_ext() {
        let nv = algebra.quiver().num_vertices();
        let n = ext.simples.len();
        for i in 0..n {
            for j in 0..n {
                if ext.dims[i][j][1] == 0 {
                    continue;
                }
                let space = ext.space(i, j, 1);
                for (b, class) in ext.basis(i, j, 1).iter().enumerate() {
                    assert_nonzero_ext1_round_trip(name, nv, i, j, b, class, space);
                }
                assert_zero_ext1_round_trip(name, i, j, space);
            }
        }
    }
}
