use super::*;

/// The Kronecker representation `(I_3, C)` over F_2 with `C` the companion
/// matrix of x^3 + x + 1, irreducible over F_2, so `End(W)` is the field
/// F_8 and the residue degree is 3. Same module as
/// `arquiver::tests::f8_module`, `indec.rs`, and `approx.rs`.
fn f8_module(algebra: &Arc<Algebra>, field: PrimeField) -> Module {
    let mut companion = DenseMat::zero(3, 3);
    companion.set(0, 1, field.one());
    companion.set(1, 2, field.one());
    companion.set(2, 0, field.one());
    companion.set(2, 1, field.one());
    Module::new(
        algebra.clone(),
        vec![3, 3],
        vec![DenseMat::identity(3), companion],
    )
    .expect("a Kronecker representation is a module")
}

// Residue degree above 1 at the pair layer. `docs/support-tau-tilting.md` section
// 8 rests field generality on residue division rings larger than the prime
// field, and the tau-rigidity condition is where they enter: it runs
// Hom(X_i, tau X_j) over the summands.
//
// W is the F_8 module, of dimension vector [3, 3] over kronecker(2, F_2).
// It is regular of defect zero, so tau W is isomorphic to W, and the
// condition-3 Hom system is Hom(W, W) = F_8, of F_2 dimension 3. The
// candidate (W + P_0, {}) has |M| + |P| = 2 = n and passes conditions 1
// and 2, so it reaches condition 3 with the F_8 system and is rejected
// there.
//
// No tau-rigid pair over kronecker(2) can hold W, and none can hold any
// other module of residue degree above 1 either: over a path algebra a
// tau-rigid indecomposable is exceptional, and an exceptional module has
// dim End = q(dim M) = 1. So the rejection is the only route residue
// degree 3 has to this layer, not a weaker version of a positive test.
#[test]
fn the_f8_module_reaches_the_tau_rigidity_condition() {
    let field = f2();
    let algebra = kronecker(2, field);
    let w = f8_module(&algebra, field);
    let decomposition = basic(&w);
    assert_eq!(decomposition.len(), 1);
    assert_eq!(decomposition.summands()[0].residue_degree(), 3);
    assert_eq!(decomposition.summands()[0].endo().dim(), 3);

    let translate = tau(&w).expect("kronecker translates");
    assert!(!translate.is_zero(), "W is not projective");
    assert_eq!(translate.dim_vector(), &[3, 3]);
    assert!(matches!(
        is_isomorphic(&w, &translate),
        Ok(IsoOutcome::Isomorphic(_))
    ));
    // The Hom system condition 3 runs is End(W) = F_8, of F_2 dimension 3.
    assert_eq!(hom_dim(&w, &translate).unwrap(), 3);

    // (W, {}) alone: the summand list is W, so the only Hom system the
    // condition runs is Hom(W, tau W) = End(W) = F_8. Condition 3 is
    // checked before the count, so the rejection names it even though
    // |M| + |P| = 1 is short of n = 2.
    let alone = expect_rejection(
        SupportTauTiltingPair::classify(basic(&w), support(&algebra, &[]))
            .expect("kronecker translates"),
    );
    assert_eq!(alone.condition(), 3);
    match &alone {
        PairRejection::NotTauRigid(witness) => {
            assert_eq!(witness.source().dim_vector(), &[3, 3]);
            assert_eq!(witness.translate().dim_vector(), &[3, 3]);
            assert!(witness.verify());
        }
        other => panic!("expected a tau-rigidity failure, got {other}"),
    }

    // (W + P_0, {}) has the count of a pair, |M| + |P| = 2 = n, and
    // Hom(0, M) = 0, so it passes conditions 1, 2, and 4 and is rejected
    // on tau-rigidity alone. tau P_0 = 0, so tau W is the only translate
    // any Hom system in the check can end at.
    let p0 = Module::projective(&algebra, 0);
    let candidate = sum(&algebra, &[&w, &p0]);
    assert_eq!(basic(&candidate).len() + support(&algebra, &[]).len(), 2);
    let rejection = expect_rejection(
        SupportTauTiltingPair::classify(basic(&candidate), support(&algebra, &[]))
            .expect("kronecker translates"),
    );
    assert_eq!(rejection.condition(), 3);
    match &rejection {
        PairRejection::NotTauRigid(witness) => {
            assert_eq!(witness.translate().dim_vector(), &[3, 3]);
            assert!(witness.verify());
        }
        other => panic!("expected a tau-rigidity failure, got {other}"),
    }
}
