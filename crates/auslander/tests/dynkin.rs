//! Dynkin and Euclidean recognition and the constructive Dynkin enumerator,
//! over F_2, F_5 and F_32003.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};

use auslander::algebra::{Algebra, an_with_relations, kronecker, path_algebra as kq};
use auslander::decompose::Certificate;
use auslander::dynkin::{
    DynkinError, DynkinType, EuclideanType, dynkin_indecomposables, dynkin_quiver, dynkin_type,
    euclidean_quiver, euclidean_type, generalized_cartan_matrix, positive_roots,
};
use auslander::ext::ext_dim;
use auslander::field::PrimeField;
use auslander::hom::hom_dim;
use auslander::iso::{IsoOutcome, is_isomorphic};
use auslander::module::Module;
use auslander::quiver::Quiver;

fn fields() -> [PrimeField; 3] {
    [
        PrimeField::new(2).unwrap(),
        PrimeField::new(5).unwrap(),
        PrimeField::new(32003).unwrap(),
    ]
}

fn path_algebra(quiver: Quiver, field: PrimeField) -> Arc<Algebra> {
    kq(quiver, field).expect("the zero ideal completes")
}

type Enumerated = (Arc<Algebra>, Arc<Vec<(Module, Certificate)>>);

/// The path algebra of `t` over `field` with its indecomposables, enumerated
/// once per (type, field) for the whole binary. Four tests read the same list,
/// and E_6 costs 36 modules on each of the three fields.
fn enumerated(t: DynkinType, field: PrimeField) -> Enumerated {
    static CACHE: OnceLock<Mutex<HashMap<(DynkinType, u64), Enumerated>>> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let mut map = cache.lock().unwrap();
    map.entry((t, field.modulus()))
        .or_insert_with(|| {
            let algebra = path_algebra(dynkin_quiver(t).unwrap(), field);
            let modules = dynkin_indecomposables(&algebra).unwrap();
            (algebra, Arc::new(modules))
        })
        .clone()
}

fn small_types() -> Vec<DynkinType> {
    vec![
        DynkinType::A(1),
        DynkinType::A(2),
        DynkinType::A(3),
        DynkinType::A(4),
        DynkinType::A(5),
        DynkinType::D(4),
    ]
}

#[test]
fn indecomposable_counts_are_n_n_plus_one_over_two_for_a_and_n_n_minus_one_for_d() {
    for field in fields() {
        for n in 1..=6 {
            let t = DynkinType::A(n);
            let (_, modules) = enumerated(t, field);
            assert_eq!(
                modules.len(),
                n * (n + 1) / 2,
                "{t} over F_{}",
                field.modulus()
            );
        }
        for n in 4..=6 {
            let t = DynkinType::D(n);
            let (_, modules) = enumerated(t, field);
            assert_eq!(modules.len(), n * (n - 1), "{t} over F_{}", field.modulus());
        }
    }
}

#[test]
fn the_exceptional_types_have_thirty_six_sixty_three_and_one_hundred_twenty_indecomposables() {
    for field in fields() {
        for (t, count) in [
            (DynkinType::E6, 36),
            (DynkinType::E7, 63),
            (DynkinType::E8, 120),
        ] {
            let (_, modules) = enumerated(t, field);
            assert_eq!(modules.len(), count, "{t} over F_{}", field.modulus());
        }
    }
}

#[test]
fn constructed_dimension_vectors_are_exactly_the_positive_roots() {
    for field in fields() {
        for t in small_types()
            .into_iter()
            .chain([DynkinType::D(5), DynkinType::E6])
        {
            let roots = positive_roots(&dynkin_quiver(t).unwrap()).unwrap();
            let built: Vec<Vec<usize>> = enumerated(t, field)
                .1
                .iter()
                .map(|(m, _)| m.dim_vector().to_vec())
                .collect();
            assert_eq!(built, roots, "{t} over F_{}", field.modulus());
        }
    }
}

#[test]
fn every_constructed_module_is_certified_indecomposable() {
    for field in fields() {
        for t in small_types().into_iter().chain([DynkinType::E6]) {
            for (m, certificate) in enumerated(t, field).1.iter() {
                assert_eq!(
                    *certificate,
                    Certificate::Indecomposable,
                    "{t} over F_{} at {:?}",
                    field.modulus(),
                    m.dim_vector()
                );
            }
        }
    }
}

#[test]
fn every_constructed_module_is_a_brick_without_self_extensions() {
    for field in fields() {
        for t in small_types().into_iter().chain([DynkinType::E6]) {
            for (m, _) in enumerated(t, field).1.iter() {
                assert_eq!(
                    hom_dim(m, m).unwrap(),
                    1,
                    "{t} over F_{} at {:?}",
                    field.modulus(),
                    m.dim_vector()
                );
                assert_eq!(
                    ext_dim(m, m, 1).unwrap(),
                    0,
                    "{t} over F_{} at {:?}",
                    field.modulus(),
                    m.dim_vector()
                );
            }
        }
    }
}

#[test]
fn constructed_modules_are_pairwise_non_isomorphic() {
    for field in fields() {
        for t in small_types() {
            let (_, modules) = enumerated(t, field);
            assert_eq!(modules.len(), t.indecomposable_count().unwrap());
            for (i, (m, _)) in modules.iter().enumerate() {
                for (n, _) in modules.iter().skip(i + 1) {
                    assert!(
                        matches!(is_isomorphic(m, n).unwrap(), IsoOutcome::NotIsomorphic(_)),
                        "{t} over F_{}: {:?} and {:?} are not separated",
                        field.modulus(),
                        m.dim_vector(),
                        n.dim_vector()
                    );
                }
            }
        }
    }
}

#[test]
fn every_projective_and_every_simple_occurs_among_the_constructed_modules() {
    for field in fields() {
        for t in [DynkinType::A(4), DynkinType::D(4)] {
            let (algebra, modules) = enumerated(t, field);
            for v in 0..algebra.quiver().num_vertices() {
                for expected in [
                    Module::projective(&algebra, v),
                    Module::injective(&algebra, v),
                    Module::simple(&algebra, v),
                ] {
                    assert!(
                        modules.iter().any(|(m, _)| matches!(
                            is_isomorphic(m, &expected).unwrap(),
                            IsoOutcome::Isomorphic(_)
                        )),
                        "{t} over F_{}: {:?} is missing",
                        field.modulus(),
                        expected.dim_vector()
                    );
                }
            }
        }
    }
}

#[test]
fn every_orientation_of_a4_gives_the_same_dimension_vectors() {
    let orientations = [
        Quiver::new(4, &[(0, 1), (1, 2), (2, 3)]).unwrap(),
        Quiver::new(4, &[(1, 0), (2, 1), (3, 2)]).unwrap(),
        Quiver::new(4, &[(0, 1), (2, 1), (2, 3)]).unwrap(),
        Quiver::new(4, &[(1, 0), (1, 2), (3, 2)]).unwrap(),
    ];
    for field in fields() {
        let mut seen: Option<Vec<Vec<usize>>> = None;
        for quiver in &orientations {
            assert_eq!(dynkin_type(quiver), Some(DynkinType::A(4)));
            let algebra = path_algebra(quiver.clone(), field);
            let dims: Vec<Vec<usize>> = dynkin_indecomposables(&algebra)
                .unwrap()
                .iter()
                .map(|(m, _)| m.dim_vector().to_vec())
                .collect();
            match &seen {
                None => seen = Some(dims),
                Some(first) => assert_eq!(first, &dims, "over F_{}", field.modulus()),
            }
        }
    }
}

#[test]
fn kronecker_2_is_euclidean_and_rejected_by_the_dynkin_enumerator() {
    for field in fields() {
        let algebra = kronecker(2, field);
        assert_eq!(euclidean_type(algebra.quiver()), Some(EuclideanType::A(1)));
        assert_eq!(dynkin_type(algebra.quiver()), None);
        assert_eq!(
            dynkin_indecomposables(&algebra).unwrap_err(),
            DynkinError::NotDynkin {
                euclidean: Some(EuclideanType::A(1)),
            }
        );
    }
}

#[test]
fn a_bound_a3_is_rejected_for_its_nonzero_ideal() {
    for field in fields() {
        let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
        assert_eq!(dynkin_type(algebra.quiver()), Some(DynkinType::A(3)));
        assert_eq!(
            dynkin_indecomposables(&algebra).unwrap_err(),
            DynkinError::NonzeroIdeal { relations: 1 }
        );
    }
}

#[test]
fn dynkin_and_euclidean_diagrams_are_recognized_and_never_confused() {
    let dynkin: Vec<DynkinType> = (1..=8)
        .map(DynkinType::A)
        .chain((4..=8).map(DynkinType::D))
        .chain([DynkinType::E6, DynkinType::E7, DynkinType::E8])
        .collect();
    for t in dynkin {
        let quiver = dynkin_quiver(t).unwrap();
        assert_eq!(dynkin_type(&quiver), Some(t));
        assert_eq!(euclidean_type(&quiver), None, "{t}");
        assert_eq!(quiver.num_vertices() as usize, t.num_vertices().unwrap());
    }
    let euclidean: Vec<EuclideanType> = (1..=8)
        .map(EuclideanType::A)
        .chain((4..=8).map(EuclideanType::D))
        .chain([EuclideanType::E6, EuclideanType::E7, EuclideanType::E8])
        .collect();
    for t in euclidean {
        let quiver = euclidean_quiver(t).unwrap();
        assert_eq!(euclidean_type(&quiver), Some(t));
        assert_eq!(dynkin_type(&quiver), None, "{t}");
        assert_eq!(positive_roots(&quiver), None, "{t}");
        assert_eq!(quiver.num_vertices() as usize, t.num_vertices().unwrap());
    }
}

/// The star with arms 2, 2, 3 is the smallest wild tree: it strictly contains
/// Euclidean E_6 (arms 2, 2, 2), so it is neither Dynkin nor Euclidean. The
/// enumerator rejects it with no Euclidean type to report, the one
/// `NotDynkin { euclidean: None }` in the fixture set.
#[test]
fn the_star_with_arms_2_2_3_is_neither_dynkin_nor_euclidean() {
    let quiver = Quiver::new(8, &[(0, 1), (1, 2), (0, 3), (3, 4), (0, 5), (5, 6), (6, 7)]).unwrap();
    assert_eq!(dynkin_type(&quiver), None);
    assert_eq!(euclidean_type(&quiver), None);
    assert_eq!(positive_roots(&quiver), None);
    for field in fields() {
        let algebra = path_algebra(quiver.clone(), field);
        assert_eq!(
            dynkin_indecomposables(&algebra).unwrap_err(),
            DynkinError::NotDynkin { euclidean: None }
        );
    }
}

/// Parameters below the documented range name no diagram, so every constructor
/// returns `None`. `D(3)` is the sharp case: as a graph the star with arms
/// 1, 1, 0 is the path `A_3`, so a `Some` there would be a live misclassification
/// rather than a missing entry.
#[test]
fn degenerate_type_parameters_name_no_diagram() {
    for t in [DynkinType::A(0), DynkinType::D(3), DynkinType::D(2)] {
        assert_eq!(t.num_vertices(), None, "{t}");
        assert_eq!(t.indecomposable_count(), None, "{t}");
        assert!(dynkin_quiver(t).is_none(), "{t}");
    }
    assert_eq!(EuclideanType::A(0).num_vertices(), None);
    assert!(euclidean_quiver(EuclideanType::A(0)).is_none());
}

/// The generalized Cartan matrix of `A_5`, written out. Every tree on `n`
/// vertices has `n - 1` edges, so counting edges cannot tell `A_5` from `D_5`;
/// the matrix itself can.
#[test]
fn the_generalized_cartan_matrix_of_a5_is_the_path_matrix() {
    let cartan = generalized_cartan_matrix(&dynkin_quiver(DynkinType::A(5)).unwrap()).unwrap();
    assert_eq!(
        cartan,
        vec![
            vec![2, -1, 0, 0, 0],
            vec![-1, 2, -1, 0, 0],
            vec![0, -1, 2, -1, 0],
            vec![0, 0, -1, 2, -1],
            vec![0, 0, 0, -1, 2],
        ]
    );
}

#[test]
fn the_generalized_cartan_matrix_is_symmetric_with_two_on_the_diagonal() {
    for t in [DynkinType::A(5), DynkinType::D(6), DynkinType::E8] {
        let cartan = generalized_cartan_matrix(&dynkin_quiver(t).unwrap()).unwrap();
        let n = cartan.len();
        assert_eq!(n, t.num_vertices().unwrap());
        let mut edges = 0;
        for (i, row) in cartan.iter().enumerate() {
            assert_eq!(row[i], 2);
            for (j, &entry) in row.iter().enumerate() {
                assert_eq!(entry, cartan[j][i]);
                if i != j {
                    assert!(entry == 0 || entry == -1);
                    edges += usize::from(i < j && entry == -1);
                }
            }
        }
        assert_eq!(edges, n - 1, "{t} is a tree");
    }
}
