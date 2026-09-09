use super::*;

// End(W) = F_8 is a field, so rad End(W) = 0 and the radical of the
// category between W and itself is zero, while Hom(W, W) has F_2
// dimension 3. Hom(W, W) and its radical are F_8 spaces, so both
// dimensions are multiples of the residue degree 3.
#[test]
fn the_radical_of_the_f8_module_is_zero_with_residue_degree_3_bookkeeping() {
    let w = indec(&f8_module());
    assert_eq!(w.residue_degree(), 3);
    assert_eq!(w.endo().radical_dim(), 0);
    let space = HomSpace::new(w.module(), w.module()).unwrap();
    assert_eq!(space.dim(), 3);
    let radical = category_radical(&w, &w).unwrap();
    assert_eq!(radical.dim(), 0);
    assert_eq!(over_residue(space.dim(), 3, w.module()).unwrap(), 1);
    assert_eq!(over_residue(radical.dim(), 3, w.module()).unwrap(), 0);
}

#[test]
fn a_residue_degree_that_does_not_divide_is_a_typed_defect() {
    let w = f8_module();
    assert_eq!(
        over_residue(2, 3, &w).unwrap_err(),
        ArQuiverError::ResidueDegreeDoesNotDivide {
            dim_vector: vec![3, 3],
            base_dim: 2,
            residue_degree: 3,
        }
    );
    assert_eq!(
        over_residue(1, 0, &w).unwrap_err(),
        ArQuiverError::ResidueDegreeDoesNotDivide {
            dim_vector: vec![3, 3],
            base_dim: 1,
            residue_degree: 0,
        }
    );
}

// No fixture in this file yields a nonzero valued Irr, and the two catalog
// domains cannot (every entry has residue degree 1), so the Valued
// arithmetic is pinned here on directly built arrows through the same
// division routine `quiver_of` calls.
#[test]
fn valued_arrow_arithmetic_and_the_division_gate_are_pinned() {
    let w = f8_module();
    let valued = ArArrow {
        source: 0,
        target: 1,
        base_dim: 6,
        over_source_residue: over_residue(6, 2, &w).unwrap(),
        over_target_residue: over_residue(6, 3, &w).unwrap(),
        representatives: Vec::new(),
    };
    assert_eq!(
        valued.valuation(),
        ArrowValuation::Valued {
            base_dim: 6,
            over_source: 3,
            over_target: 2,
        }
    );
    let one_sided = ArArrow {
        source: 0,
        target: 1,
        base_dim: 6,
        over_source_residue: over_residue(6, 1, &w).unwrap(),
        over_target_residue: over_residue(6, 3, &w).unwrap(),
        representatives: Vec::new(),
    };
    assert_eq!(
        one_sided.valuation(),
        ArrowValuation::Valued {
            base_dim: 6,
            over_source: 6,
            over_target: 2,
        }
    );
    let plain = ArArrow {
        source: 0,
        target: 1,
        base_dim: 6,
        over_source_residue: over_residue(6, 1, &w).unwrap(),
        over_target_residue: over_residue(6, 1, &w).unwrap(),
        representatives: Vec::new(),
    };
    assert_eq!(plain.valuation(), ArrowValuation::Plain(6));
    assert_eq!(
        over_residue(5, 3, &w).unwrap_err(),
        ArQuiverError::ResidueDegreeDoesNotDivide {
            dim_vector: vec![3, 3],
            base_dim: 5,
            residue_degree: 3,
        }
    );
}
