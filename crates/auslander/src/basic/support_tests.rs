use super::*;

#[test]
fn projective_support_sorts_and_deduplicates() {
    let algebra = linear_an(3, f5());
    let s = support(&algebra, &[2, 0, 2, 1, 0]);
    assert_eq!(s.vertices(), &[0, 1, 2]);
    assert_eq!(s.len(), 3);
    assert!(!s.is_empty());
    assert!(s.contains(0) && s.contains(1) && s.contains(2));
    assert!(!s.contains(3));
    assert_eq!(support(&algebra, &[]).len(), 0);
    assert!(support(&algebra, &[]).is_empty());
}

#[test]
fn an_out_of_range_support_vertex_is_rejected() {
    let algebra = linear_an(3, f5());
    assert_eq!(
        ProjectiveSupport::new(&algebra, &[0, 3]).unwrap_err(),
        BasicError::VertexOutOfRange {
            vertex: 3,
            num_vertices: 3
        }
    );
}

// Over A_3, P_0 = [1, 1, 1] and P_2 = [0, 0, 1], so the support {0, 2}
// rebuilds a module of dimension vector [1, 1, 2] with two summands.
#[test]
fn the_support_module_is_the_sum_of_its_projectives() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let s = support(&algebra, &[2, 0]);
        let module = s.module();
        assert_eq!(module.dim_vector(), &[1, 1, 2]);
        let decomposition = basic(&module);
        assert_eq!(
            decomposition.dim_vectors(),
            vec![vec![0, 0, 1], vec![1, 1, 1]]
        );
        assert!(support(&algebra, &[]).module().is_zero());
    }
}

#[test]
fn support_equality_is_set_equality_and_compatibility_is_separate() {
    let algebra = linear_an(3, f5());
    let other = linear_an(3, f5());
    assert_eq!(support(&algebra, &[1, 0]), support(&algebra, &[0, 1, 0]));
    assert_ne!(support(&algebra, &[1]), support(&algebra, &[2]));
    // Equality ignores the algebra; is_compatible is what separates two
    // algebra values built from the same presentation.
    assert_eq!(support(&algebra, &[1]), support(&other, &[1]));
    assert!(support(&algebra, &[1]).is_compatible(&support(&algebra, &[2])));
    assert!(!support(&algebra, &[1]).is_compatible(&support(&other, &[1])));
}
