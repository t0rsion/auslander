use super::*;

#[test]
fn isomorphic_pairs_have_equal_fingerprints() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let p2 = Module::projective(&algebra, 2);
        let first = basic(&sum(&[&p0, &p2]));
        let second = basic(&sum(&[&p2, &p0]));
        let s = support(&algebra, &[1]);
        assert_eq!(
            PairFingerprint::new(&first, &s).unwrap(),
            PairFingerprint::new(&second, &s).unwrap(),
            "over F_{}",
            field.modulus()
        );
    }
}

// The fingerprint separates on the projective support, on the summand
// count, and on the summand dimension vectors.
#[test]
fn fingerprints_separate_obviously_different_pairs() {
    let algebra = linear_an(3, f5());
    let p0 = basic(&Module::projective(&algebra, 0));
    let p1 = basic(&Module::projective(&algebra, 1));
    let both = basic(&sum(&[
        &Module::projective(&algebra, 0),
        &Module::projective(&algebra, 2),
    ]));
    let left = support(&algebra, &[1]);
    let right = support(&algebra, &[2]);
    let base = PairFingerprint::new(&p0, &left).unwrap();
    assert_ne!(base, PairFingerprint::new(&p0, &right).unwrap());
    assert_ne!(base, PairFingerprint::new(&p1, &left).unwrap());
    assert_ne!(base, PairFingerprint::new(&both, &left).unwrap());
    assert_eq!(base.projective_support(), &[1]);
    assert_eq!(base.summands().len(), 1);
}

// P_0 over A_3 is uniserial with top S_0 and socle S_2, Loewy length 3,
// and End(P_0) = k. Hom(S_v, P_0) is 1 at v = 2 and 0 elsewhere, because
// the only simple submodule is the socle; Hom(P_0, S_v) is 1 at v = 0 and
// 0 elsewhere, because a map out of a projective is fixed by the top.
#[test]
fn the_a3_regular_projective_fingerprint_is_hand_checkable() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let p0 = basic(&Module::projective(&algebra, 0));
        let s = support(&algebra, &[]);
        let fingerprint = PairFingerprint::new(&p0, &s).unwrap();
        let record = &fingerprint.summands()[0];
        assert_eq!(record.dim_vector(), &[1, 1, 1]);
        assert_eq!(record.loewy_length(), 3);
        assert_eq!(record.top_dim_vector(), &[1, 0, 0]);
        assert_eq!(record.socle_dim_vector(), &[0, 0, 1]);
        assert_eq!(record.end_dim(), 1);
        assert_eq!(record.residue_degree(), 1);
        assert_eq!(record.hom_from_simples(), &[0, 0, 1]);
        assert_eq!(
            record.hom_to_simples(),
            &[1, 0, 0],
            "over F_{}",
            field.modulus()
        );
        assert!(fingerprint.projective_support().is_empty());
    }
}

// The three [1, 1] Kronecker modules over F_2 share every fingerprint
// field. Each has Loewy length 2 with top [1, 0] and socle [0, 1], End is
// F_2, and the Hom profile against the simples is
// hom(S_0, X) = 0, hom(S_1, X) = 1, hom(X, S_0) = 1, hom(X, S_1) = 0,
// because each module has a nonzero arrow map. Only pair_iso separates
// them.
#[test]
fn the_kronecker_line_modules_collide_in_the_fingerprint() {
    let field = f2();
    let algebra = kronecker(2, field);
    let modules = [
        kronecker_line(&algebra, field, 1, 0),
        kronecker_line(&algebra, field, 0, 1),
        kronecker_line(&algebra, field, 1, 1),
    ];
    let empty = support(&algebra, &[]);
    let decompositions: Vec<BasicDecomposition> = modules.iter().map(basic).collect();
    for decomposition in &decompositions {
        assert_eq!(decomposition.len(), 1);
        assert_eq!(decomposition.dim_vectors(), vec![vec![1, 1]]);
    }
    let fingerprints: Vec<PairFingerprint> = decompositions
        .iter()
        .map(|d| PairFingerprint::new(d, &empty).unwrap())
        .collect();
    assert_eq!(fingerprints[0], fingerprints[1]);
    assert_eq!(fingerprints[0], fingerprints[2]);
    let record = &fingerprints[0].summands()[0];
    assert_eq!(record.loewy_length(), 2);
    assert_eq!(record.top_dim_vector(), &[1, 0]);
    assert_eq!(record.socle_dim_vector(), &[0, 1]);
    assert_eq!(record.end_dim(), 1);
    assert_eq!(record.hom_from_simples(), &[0, 1]);
    assert_eq!(record.hom_to_simples(), &[1, 0]);
    for i in 0..3 {
        for j in 0..3 {
            let outcome = pair_iso(&decompositions[i], &empty, &decompositions[j], &empty).unwrap();
            if i == j {
                assert!(expect_witness(outcome).verify());
            } else {
                assert_eq!(
                    expect_obstruction(outcome),
                    SupportPairObstruction::UnmatchedSummand {
                        index: 0,
                        dim_vector: vec![1, 1]
                    },
                    "the [1, 1] modules {i} and {j} are not isomorphic"
                );
            }
        }
    }
}

/// A xorshift64 generator, seeded by the caller so every basis change
/// below is the same draw on every run and every platform.
struct XorShift64(u64);

impl XorShift64 {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn below(&mut self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.next() % n }
    }
}

/// A `d` by `d` invertible matrix, built by elementary row operations on
/// the identity, so it is invertible whatever the draws are.
fn invertible(rng: &mut XorShift64, field: &PrimeField, d: usize) -> DenseMat {
    let mut g = DenseMat::identity(d);
    if d == 0 {
        return g;
    }
    for _ in 0..2 * d + 2 {
        let i = rng.below(d as u64) as usize;
        if d == 1 || rng.below(3) == 0 {
            let c = field.elem(1 + rng.below(field.modulus() - 1) as i64);
            for k in 0..d {
                g.set(i, k, field.mul(g.get(i, k), c));
            }
            continue;
        }
        let j = (i + 1 + rng.below(d as u64 - 1) as usize) % d;
        if rng.below(2) == 0 {
            for k in 0..d {
                let (a, b) = (g.get(i, k), g.get(j, k));
                g.set(i, k, b);
                g.set(j, k, a);
            }
        } else {
            let c = field.elem(rng.below(field.modulus()) as i64);
            for k in 0..d {
                g.set(i, k, field.add(g.get(i, k), field.mul(c, g.get(j, k))));
            }
        }
    }
    g
}

/// `M'(a) = G_{s(a)} M(a) G_{t(a)}^{-1}` for one invertible `G_v` per
/// vertex, so `M'` is isomorphic to `m` and carries other arrow matrices.
fn basis_change(rng: &mut XorShift64, m: &Module) -> Module {
    let field = m.field();
    let quiver = m.algebra().quiver();
    let g: Vec<DenseMat> = m
        .dim_vector()
        .iter()
        .map(|&d| invertible(rng, &field, d))
        .collect();
    let g_inv: Vec<DenseMat> = g
        .iter()
        .map(|x| {
            x.inverse(&field)
                .expect("elementary operations stay invertible")
        })
        .collect();
    let maps: Vec<DenseMat> = (0..quiver.num_arrows())
        .map(|i| {
            let a = ArrowId(i as u32);
            let (s, t) = (quiver.source(a) as usize, quiver.target(a) as usize);
            g[s].mul(m.map(a), &field).mul(&g_inv[t], &field)
        })
        .collect();
    Module::new(m.algebra().clone(), m.dim_vector().to_vec(), maps)
        .expect("a vertexwise basis change preserves the relations")
}

// Soundness of the prefilter, which the completeness certificate rests on.
// `CatalogEnumeration::verify` skips the certified pair_iso test whenever
// two fingerprints differ, so a fingerprint that separated two isomorphic
// pairs would let a duplicate vertex through unseen.
//
// `isomorphic_pairs_have_equal_fingerprints` cannot catch that: it builds
// both sides from the same two Module values, and PairFingerprint::new
// sorts its summand records, so that test passes even when every invariant
// is computed wrongly. This one rebuilds each module part in another basis.
// `M'(a) = G_{s(a)} M(a) G_{t(a)}^{-1}` is isomorphic to `M` and carries
// other arrow matrices, so an invariant computed from the matrices rather
// than from the isomorphism class moves and the fingerprints separate.
//
// The 50 D_4 pairs are the fixture the design's selectivity claim is
// stated on (section 4: 50 of 2500 comparisons admitted on D_4).
#[test]
fn the_fingerprint_is_constant_on_isomorphism_classes() {
    let field = f5();
    let algebra = d4(field);
    let catalog = IndecomposableCatalog::dynkin(&algebra).expect("D_4 is Dynkin");
    let enumeration = enumerate_over_catalog(&catalog).expect("D_4 enumerates");
    assert_eq!(enumeration.len(), 50);

    let mut rng = XorShift64(0x5eed_0005_0005_0001);
    let mut fingerprints = Vec::with_capacity(enumeration.len());
    let mut moved = 0;
    for pair in enumeration.pairs() {
        let before = PairFingerprint::new(pair.module(), &pair.projective()).unwrap();
        let module = pair.module().module();
        let rebuilt = basis_change(&mut rng, module);
        let decomposition =
            BasicDecomposition::new(&rebuilt).expect("a basis change keeps the module basic");
        let after = PairFingerprint::new(&decomposition, &pair.projective()).unwrap();
        assert_eq!(
            before,
            after,
            "the fingerprint moved under a basis change of {:?}",
            pair.module().dim_vectors()
        );
        let arrows = 0..algebra.quiver().num_arrows();
        let same: Vec<bool> = arrows
            .map(|i| {
                let a = ArrowId(i as u32);
                rebuilt.map(a) == module.map(a)
            })
            .collect();
        if same.iter().all(|&s| s) {
            // Nothing moved, so this pair carries no evidence. Every arrow
            // of D_4 runs from the center to a leaf, so a module part with
            // a zero dimension at the center or at every leaf has only
            // empty arrow matrices and no basis change can act on it.
            for i in 0..algebra.quiver().num_arrows() {
                let matrix = module.map(ArrowId(i as u32));
                assert!(
                    matrix.rows() == 0 || matrix.cols() == 0,
                    "a nonempty arrow matrix survived the basis change in {:?}",
                    pair.module().dim_vectors()
                );
            }
        } else {
            moved += 1;
        }
        fingerprints.push(before);
    }
    // The 9 unmoved module parts are the 8 sums of the leaf simples S_1,
    // S_2, S_3 (the empty sum included) and S_0 on its own. The seed fixes
    // which basis change each of the other 41 got.
    assert_eq!(moved, 41);

    // The design's selectivity claim, section 4: on D_4 the prefilter
    // admits only self-matches, 50 of the 50 * 50 ordered comparisons.
    let mut admitted = 0;
    for (i, left) in fingerprints.iter().enumerate() {
        for (j, right) in fingerprints.iter().enumerate() {
            if left == right {
                admitted += 1;
                assert_eq!(i, j, "pairs {i} and {j} share a fingerprint");
            }
        }
    }
    assert_eq!(admitted, 50);
}

// Residue degree is the one fingerprint field that needs a division ring
// larger than the prime field to say anything, and `docs/support-tau-tilting.md`
// section 8 rests field generality on exactly that. Both modules here are
// Kronecker representations `(I_3, B)` over F_2 with dimension vector
// [3, 3]:
//
// - W takes B the companion matrix of x^3 + x + 1, irreducible over F_2,
//   so End(W) = F_2[B] is the field F_8 and the residue degree is 3. Same
//   module as `arquiver::tests::f8_module`, `indec.rs`, and `approx.rs`.
// - J takes B the nilpotent Jordan block of size 3, so End(J) = F_2[B] is
//   F_2[x]/(x^3), local with residue field F_2 and residue degree 1.
//
// Both have End of F_2 dimension 3, and the first arrow acts invertibly in
// both, so both have Loewy length 2, top [3, 0], and socle [0, 3]. The Hom
// profiles against the simples agree too. Residue degree is the only field
// that separates them.
#[test]
fn the_fingerprint_separates_on_residue_degree() {
    let field = f2();
    let algebra = kronecker(2, field);
    let mut companion = DenseMat::zero(3, 3);
    companion.set(0, 1, field.one());
    companion.set(1, 2, field.one());
    companion.set(2, 0, field.one());
    companion.set(2, 1, field.one());
    let w = Module::new(
        algebra.clone(),
        vec![3, 3],
        vec![DenseMat::identity(3), companion],
    )
    .expect("a Kronecker representation is a module");
    let mut jordan = DenseMat::zero(3, 3);
    jordan.set(0, 1, field.one());
    jordan.set(1, 2, field.one());
    let j = Module::new(
        algebra.clone(),
        vec![3, 3],
        vec![DenseMat::identity(3), jordan],
    )
    .expect("a Kronecker representation is a module");

    let empty = support(&algebra, &[]);
    let f8 = PairFingerprint::new(&basic(&w), &empty).unwrap();
    let f2_residue = PairFingerprint::new(&basic(&j), &empty).unwrap();
    let (left, right) = (&f8.summands()[0], &f2_residue.summands()[0]);
    assert_eq!(left.residue_degree(), 3);
    assert_eq!(right.residue_degree(), 1);
    assert_ne!(f8, f2_residue, "residue degree is the separating field");

    // Every other field agrees, so nothing else could have separated them.
    assert_eq!(left.dim_vector(), right.dim_vector());
    assert_eq!(left.dim_vector(), &[3, 3]);
    assert_eq!(left.loewy_length(), right.loewy_length());
    assert_eq!(left.loewy_length(), 2);
    assert_eq!(left.top_dim_vector(), right.top_dim_vector());
    assert_eq!(left.top_dim_vector(), &[3, 0]);
    assert_eq!(left.socle_dim_vector(), right.socle_dim_vector());
    assert_eq!(left.socle_dim_vector(), &[0, 3]);
    assert_eq!(left.end_dim(), right.end_dim());
    assert_eq!(left.end_dim(), 3);
    assert_eq!(left.hom_from_simples(), right.hom_from_simples());
    assert_eq!(left.hom_from_simples(), &[0, 3]);
    assert_eq!(left.hom_to_simples(), right.hom_to_simples());
    assert_eq!(left.hom_to_simples(), &[3, 0]);
}
