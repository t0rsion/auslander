use std::fmt::Write;
use std::sync::{Arc, OnceLock};

use super::stages::{Partition, SeparationTable};
use super::*;
use crate::algebra::{commutative_square, linear_an, monomial_algebra, path_algebra};
use crate::derived_invariant::InvariantReading;
use crate::equivalence_discovery::DiscoveryLimits;
use crate::field::PrimeField;
use crate::gentle::connected_gentle_algebras;
use crate::hochschild::BarLimits;
use crate::monomial::MonomialIdeal;
use crate::quiver::{ArrowId, Quiver};

fn f2() -> PrimeField {
    PrimeField::new(2).unwrap()
}

pub(super) fn limits() -> ClassificationLimits {
    ClassificationLimits {
        invariants: InvariantLimits {
            hochschild_degree: 2,
            bar: BarLimits {
                max_tensor_tuples: 10_000,
                max_cochain_dim: 100_000,
                max_matrix_entries: 10_000_000,
                max_work_units: 1_000_000_000,
            },
        },
        discovery: DiscoveryLimits {
            max_vertices: 8,
            max_directed_mutations: 32,
            max_total_terms: 256,
            max_matrix_entries: 16_384,
            ..DiscoveryLimits::default()
        },
        target: TargetLimits::default(),
    }
}

pub(super) fn classify(family: &[Arc<Algebra>]) -> DerivedClassification {
    classify_derived(family, &limits(), &ComputationControl::new()).unwrap()
}

/// The connected gentle algebras with `n` vertices over `F_2`.
fn gentle(n: u32) -> Vec<Arc<Algebra>> {
    connected_gentle_algebras(n, f2()).unwrap()
}

/// The classifications of the connected gentle algebras with 1, 2, and 3
/// vertices over `F_2`, computed once per test binary.
pub(super) fn corpus() -> &'static [DerivedClassification] {
    static CORPUS: OnceLock<Vec<DerivedClassification>> = OnceLock::new();
    CORPUS.get_or_init(|| (1..=3).map(|n| classify(&gentle(n))).collect())
}

/// The monomial algebra with quadratic zero relations `(first, second)`.
fn bound(vertices: u32, arrows: &[(u32, u32)], relations: &[(u32, u32)]) -> Arc<Algebra> {
    let quiver = Quiver::new(vertices, arrows).unwrap();
    let words = relations
        .iter()
        .map(|&(first, second)| vec![ArrowId(first), ArrowId(second)])
        .collect();
    monomial_algebra(&MonomialIdeal::new(quiver, words).unwrap(), f2()).unwrap()
}

/// Every stored decision, in order, without the algebras themselves.
pub(super) fn outline(result: &DerivedClassification) -> String {
    let mut text = format!("groups {:?}\n", result.groups());
    for class in result.classes() {
        writeln!(text, "class {:?}", class.members()).unwrap();
        for merge in class.merges() {
            let recipe: Vec<_> = merge
                .recipe()
                .iter()
                .map(|step| (step.direction(), step.summand()))
                .collect();
            let isomorphism = merge.isomorphism();
            writeln!(
                text,
                "  merge {} -> {} {recipe:?} {:?} {:?}",
                merge.source(),
                merge.member(),
                isomorphism.vertex_map(),
                isomorphism.arrow_images()
            )
            .unwrap();
        }
    }
    for separation in result.separations() {
        let witness = separation.witness();
        writeln!(
            text,
            "separate {:?} {:?} {:?} {:?} {:?}",
            separation.classes(),
            separation.members(),
            witness.kind(),
            witness.left_value(),
            witness.right_value()
        )
        .unwrap();
    }
    writeln!(text, "{:?}\n{:?}", result.unresolved(), result.walks()).unwrap();
    text
}

/// Every corpus run returns `Ok`, so [`ClassificationError::Contradiction`]
/// never fires on it: no match leaves its group or joins separated members.
#[test]
fn status_and_counts_are_pinned() {
    // members, groups, classes, separations, unresolved, walks, merges
    // With n = 3, the walks from members 9 and 45 reach members 46 and 47,
    // so those two have no unresolved partner left and are not walked. The
    // winding class separates members 68 and 70, so neither is walked.
    let expected = [
        [2, 2, 2, 1, 0, 0, 0],
        [9, 8, 8, 28, 0, 1, 1],
        [77, 30, 30, 435, 0, 21, 47],
    ];
    for (result, expected) in corpus().iter().zip(expected) {
        let merges: usize = result.classes().iter().map(|c| c.merges().len()).sum();
        let counts = [
            result.family().len(),
            result.groups().len(),
            result.classes().len(),
            result.separations().len(),
            result.unresolved().len(),
            result.walks().len(),
            merges,
        ];
        assert_eq!(counts, expected);
        assert!(result.verify());
    }
    let statuses: Vec<_> = corpus().iter().map(DerivedClassification::status).collect();
    assert!(
        statuses
            .iter()
            .all(|&s| s == ClassificationStatus::Complete)
    );
}

/// Members 68 and 70 with 3 vertices are genus-1 gentle algebras with the
/// AAG function `[(2, 4)]`. No walk joins them, and their winding classes
/// differ, so the winding class separates them.
#[test]
fn the_winding_class_separates_the_genus_one_pair() {
    let result = &corpus()[2];
    let separation = result
        .separations()
        .iter()
        .find(|s| {
            let (left, right) = s.classes();
            result.classes()[left].members() == [68] && result.classes()[right].members() == [70]
        })
        .expect("members 68 and 70 are separated");
    assert_eq!(
        separation.witness().kind(),
        DerivedInvariantKind::WindingClass
    );
    assert!(separation.witness().verify());
}

/// Assem and Happel: a gentle algebra is derived equivalent to `A_n` exactly
/// when its quiver is a tree. The trees are the members with `n - 1` arrows.
#[test]
fn gentle_trees_form_the_class_of_a_n() {
    for result in corpus() {
        let trees: Vec<usize> = (0..result.family().len())
            .filter(|&m| {
                let quiver = result.family()[m].quiver();
                quiver.num_arrows() + 1 == quiver.num_vertices() as usize
            })
            .collect();
        let class = result
            .classes()
            .iter()
            .find(|class| class.members().contains(&trees[0]))
            .unwrap();
        assert_eq!(class.members(), trees);
    }
    assert_eq!(corpus()[2].classes()[0].members().len(), 4);
}

#[test]
fn invariants_never_contradict_merges() {
    for result in corpus() {
        let invariants = result.invariants();
        for class in result.classes() {
            for &left in class.members() {
                for &right in class.members() {
                    let difference = first_difference(&invariants[left], &invariants[right]);
                    assert_eq!(difference, None, "members {left} and {right}");
                }
            }
        }
        for separation in result.separations() {
            let (left, right) = separation.classes();
            assert!(left < right);
        }
    }
}

#[test]
fn identical_input_gives_identical_output() {
    let again = classify(&gentle(3));
    assert_eq!(outline(&again), outline(&corpus()[2]));
}

#[test]
fn tampered_merges_fail_verify() {
    let result = &corpus()[2];
    let (class, merge) = result
        .classes()
        .iter()
        .enumerate()
        .find_map(|(c, class)| {
            Some((
                c,
                class.merges().iter().position(|m| !m.recipe().is_empty())?,
            ))
        })
        .unwrap();
    let tamper = |edit: &dyn Fn(&mut DerivedMerge)| {
        let mut tampered = result.clone();
        edit(&mut tampered.classes[class].merges[merge]);
        tampered.verify()
    };
    let other = result.classes()[class + 1..]
        .iter()
        .find_map(|class| class.merges().first())
        .unwrap()
        .clone();
    assert!(!tamper(&|m| m
        .recipe
        .push(ArtifactMutation::new(m.recipe[0].direction(), 99))));
    assert!(!tamper(&|m| m.recipe.clear()));
    assert!(!tamper(&|m| m.isomorphism.arrow_images[0].fill(f2().zero())));
    assert!(!tamper(&|m| m.isomorphism.vertex_map.reverse()));
    assert!(!tamper(&|m| m.path = other.path.clone()));
    assert!(!tamper(&|m| m.member = other.member));
    let mut moved = result.clone();
    let member = moved.classes[class].members.pop().unwrap();
    moved.classes[class + 1].members.push(member);
    assert!(!moved.verify());
}

#[test]
fn tampered_separations_fail_verify() {
    let result = &corpus()[1];
    let tamper = |edit: &dyn Fn(&mut DerivedClassification)| {
        let mut tampered = result.clone();
        edit(&mut tampered);
        tampered.verify()
    };
    assert!(tamper(&|_| {}));
    assert!(!tamper(&|r| r.separations.swap(0, 1)));
    assert!(!tamper(
        &|r| r.separations[0].members = (r.separations[0].members.1, 0)
    ));
    assert!(!tamper(
        &|r| r.separations[0].witness = r.separations[1].witness.clone()
    ));
    assert!(!tamper(&|r| {
        r.separations.pop();
    }));
    assert!(!tamper(&|r| {
        let pair = UnresolvedPair {
            classes: r.separations[0].classes,
            walks: Vec::new(),
        };
        r.unresolved.push(pair);
    }));
}

#[test]
fn mixed_fields_are_rejected() {
    let family = [
        linear_an(2, f2()),
        linear_an(2, PrimeField::new(3).unwrap()),
    ];
    let error = classify_derived(&family, &limits(), &ComputationControl::new()).unwrap_err();
    assert!(matches!(
        error,
        ClassificationError::FieldMismatch(FamilyFieldError {
            member: 1,
            expected: 2,
            found: 3
        })
    ));
}

/// The commutative square is not gentle and has the Cartan data of `D_4`.
/// Its duplicate merges by certificate, and `A_4` separates by the factors
/// of `C + C^T`. The square is derived equivalent to the `D_4` path
/// algebra, but no recovered target has the certificate of either, so that
/// pair stays open.
#[test]
fn a_non_gentle_member_reads_not_applicable() {
    let d4 = path_algebra(Quiver::new(4, &[(0, 3), (1, 3), (2, 3)]).unwrap(), f2()).unwrap();
    let family = [
        commutative_square(f2()),
        linear_an(4, f2()),
        commutative_square(f2()),
        d4,
    ];
    let result = classify(&family);
    assert!(result.verify());
    for member in [0, 3] {
        assert!(matches!(
            result.invariants()[member].reading(DerivedInvariantKind::AagFunction),
            InvariantReading::NotApplicable(_)
        ));
    }
    let classes: Vec<_> = result
        .classes()
        .iter()
        .map(|c| c.members().to_vec())
        .collect();
    assert_eq!(classes, [vec![0, 2], vec![1], vec![3]]);
    assert!(result.classes()[0].merges()[0].is_duplicate());
    let [open] = result.unresolved() else {
        panic!("one unresolved pair expected");
    };
    assert_eq!((open.classes(), open.walks()), ((0, 2), &[0, 1][..]));
    let kinds: Vec<_> = result
        .separations()
        .iter()
        .map(|s| s.witness().kind())
        .collect();
    assert!(!kinds.contains(&DerivedInvariantKind::AagFunction));
}

/// Members 470 and 724 of `connected_gentle_algebras(4, F_2)`. They share
/// every invariant, and no chain of tilting mutations from either one
/// reaches the other.
pub(super) fn silting_pair() -> [Arc<Algebra>; 2] {
    [
        bound(
            4,
            &[(0, 1), (0, 2), (3, 1), (2, 3), (2, 3)],
            &[(1, 4), (4, 2)],
        ),
        bound(
            4,
            &[(0, 1), (1, 2), (0, 1), (2, 3), (2, 3)],
            &[(0, 1), (1, 4)],
        ),
    ]
}

/// Walk limits under which a silting walk merges [`silting_pair`].
pub(super) fn silting_limits() -> ClassificationLimits {
    let mut limits = limits();
    limits.discovery = DiscoveryLimits {
        max_vertices: 32,
        max_directed_mutations: 128,
        max_total_terms: 1_024,
        max_matrix_entries: 65_536,
        through_silting: true,
        ..DiscoveryLimits::default()
    };
    limits
}

/// A tilting walk leaves [`silting_pair`] open. A walk through silting
/// complexes merges it, and the merge recipe replays.
#[test]
fn a_walk_through_silting_complexes_merges_an_open_pair() {
    let family = silting_pair();
    assert_eq!(classify(&family).unresolved().len(), 1);
    let control = ComputationControl::new();
    let result = classify_derived(&family, &silting_limits(), &control).unwrap();
    assert_eq!(result.status(), ClassificationStatus::Complete);
    assert_eq!(result.classes().len(), 1);
    assert!(result.verify());
}

#[test]
fn cancellation_gives_a_typed_partial_result() {
    let control = ComputationControl::new();
    control.cancel();
    let result = classify_derived(&gentle(3), &limits(), &control).unwrap();
    assert!(result.verify());
    assert_eq!(result.status(), ClassificationStatus::Incomplete);
    for walk in result.walks() {
        assert_eq!(
            walk.stop(),
            &DiscoveryStop::Cancelled {
                completed_mutations: 0
            }
        );
        assert_eq!((walk.examined(), walk.merges()), (0, 0));
    }
    for pair in result.unresolved() {
        assert!(!pair.walks().is_empty());
    }
    for separation in result.separations() {
        assert!(separation.witness().kind() < DerivedInvariantKind::HochschildDimensions);
    }
}

/// `A_3` and the 3-cycle with one relation differ in the AAG function, so a
/// merge between them is a defect.
#[test]
fn a_merge_across_separated_members_is_a_defect() {
    let family = [
        linear_an(3, f2()),
        bound(3, &[(0, 1), (1, 2), (2, 0)], &[(0, 1)]),
    ];
    let invariants: Vec<_> = family
        .iter()
        .map(|a| DerivedInvariants::compute(a, limits().invariants, &ComputationControl::new()))
        .collect::<Result<_, _>>()
        .unwrap();
    let table = SeparationTable::new(&invariants);
    let index = FamilyIndex::new(&family).unwrap();
    let mut partition = Partition::new(2);
    assert!(!partition.has_open_partner(&table, 0));
    let error = partition.merge_duplicate(&table, &index, 0, 1).unwrap_err();
    assert!(matches!(
        error,
        ClassificationError::Contradiction {
            source: 0,
            vertex: None,
            member: 1,
            separated: (0, 1),
            kind: DerivedInvariantKind::AagFunction,
        }
    ));
}

/// The structure checks read untrusted atlas data, so a long chain of merges
/// or a huge class count must cost near-linear time and no quadratic table.
#[test]
fn structure_checks_scale_on_untrusted_input() {
    use super::verify::{covers_pairs, spanning_tree};
    let members: Vec<usize> = (0..20_000).collect();
    let chain: Vec<_> = members.windows(2).map(|pair| (pair[1], pair[0])).collect();
    assert!(spanning_tree(&members, chain.iter().copied()));
    let mut cycle = chain.clone();
    cycle[19_000] = (3, 7);
    assert!(!spanning_tree(&members, cycle.into_iter()));
    assert!(!spanning_tree(&members, chain[1..].iter().copied()));
    assert!(!spanning_tree(&[2, 5], [(2, 6)].into_iter()));
    assert!(!spanning_tree(&[], std::iter::empty()));
    assert!(spanning_tree(&[4], std::iter::empty()));

    assert!(!covers_pairs(1 << 32, std::iter::empty(), &[]));
    assert!(!covers_pairs(usize::MAX, std::iter::once((0, 1)), &[]));
    let open = |classes| UnresolvedPair {
        classes,
        walks: Vec::new(),
    };
    let separated = [(0, 1), (1, 2)];
    assert!(covers_pairs(3, separated.into_iter(), &[open((0, 2))]));
    assert!(!covers_pairs(3, separated.into_iter(), &[open((1, 2))]));
    assert!(!covers_pairs(3, separated.into_iter(), &[open((0, 3))]));
    assert!(!covers_pairs(
        3,
        [(1, 2), (0, 1)].into_iter(),
        &[open((0, 2))]
    ));
}
