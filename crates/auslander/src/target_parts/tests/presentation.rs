use super::*;

#[test]
fn the_projective_generator_has_a_verified_split_target() {
    let algebra = linear_an(3, f5());
    let tilting = tilting(&regular(&algebra));
    let outcome = present_target(&tilting, &TargetLimits::default()).unwrap();
    let target = outcome.presented().expect("the regular target is split");
    assert!(target.verify());
    assert_eq!(target.target().dim(), algebra.dim());
    assert_eq!(target.split().summands().len(), 3);
    assert_eq!(target.normal_word_images().rows(), target.target().dim());
    let unit = vec![f5().one(); target.target().quiver().num_vertices() as usize];
    let mut coordinates = vec![f5().zero(); target.target().dim()];
    coordinates[..unit.len()].copy_from_slice(&unit);
    let image = target.map_coordinates(&coordinates);
    assert_eq!(image, target.endo().one());
    assert_eq!(target.preimage_coordinates(&image), coordinates);
    assert!(outcome.verify());
}

#[test]
fn the_dual_numbers_target_keeps_its_quadratic_relation() {
    let algebra = dual_numbers(f5());
    let tilting = tilting(&regular(&algebra));
    let outcome = present_target(&tilting, &TargetLimits::default()).unwrap();
    let target = outcome.presented().expect("the regular target is split");
    assert!(target.verify());
    assert_eq!(target.target().quiver().num_arrows(), 1);
    assert!(
        target
            .completion_certificate()
            .input_relations
            .iter()
            .any(|relation| relation.iter().any(|(_, word)| word.len() == 2))
    );
    assert_eq!(
        target.work(),
        TargetWork {
            endo_dimension: 2,
            radical_products: 3,
            paths: 1,
            relation_terms: 1,
        }
    );
}

#[test]
fn a_nontrivial_tilting_target_uses_the_opposite_orientation() {
    let algebra = linear_an(2, f5());
    let p0 = Module::projective(&algebra, 0);
    let s0 = Module::simple(&algebra, 0);
    let module = direct_sum(&[&p0, &s0]).0;
    let tilting = tilting(&module);
    let outcome = present_target(&tilting, &TargetLimits::default()).unwrap();
    let target = outcome.presented().expect("the tilting target is split");
    assert!(target.verify());
    assert_eq!(target.target().quiver().num_arrows(), 1);
    assert_eq!(target.target().quiver().arrows(), &[(1, 0)]);
}

#[test]
fn the_private_mutation_corpus_rejects_every_target_claim() {
    let algebra = dual_numbers(f5());
    let tilting = tilting(&regular(&algebra));
    let outcome = present_target(&tilting, &TargetLimits::default()).unwrap();
    let target = outcome.presented().expect("the regular target is split");
    let mut corpus = Vec::new();

    let mut changed = target.clone();
    let entry = changed.idempotent_images.get(0, 0);
    changed
        .idempotent_images
        .set(0, 0, f5().add(entry, f5().one()));
    corpus.push(changed);

    let mut changed = target.clone();
    let entry = changed.arrow_images.get(0, 0);
    changed.arrow_images.set(0, 0, f5().add(entry, f5().one()));
    corpus.push(changed);

    let mut changed = target.clone();
    let entry = changed.normal_word_images.get(0, 0);
    changed
        .normal_word_images
        .set(0, 0, f5().add(entry, f5().one()));
    corpus.push(changed);

    let mut changed = target.clone();
    let entry = changed.normal_word_preimages.get(0, 0);
    changed
        .normal_word_preimages
        .set(0, 0, f5().add(entry, f5().one()));
    corpus.push(changed);

    let mut changed = target.clone();
    changed.work.endo_dimension += 1;
    corpus.push(changed);

    let mut changed = target.clone();
    changed.work.radical_products += 1;
    corpus.push(changed);

    let mut changed = target.clone();
    changed.work.paths += 1;
    corpus.push(changed);

    let mut changed = target.clone();
    changed.work.relation_terms += 1;
    corpus.push(changed);

    let mut changed = target.clone();
    changed.completion.input_relations[0][0].0 = 2;
    corpus.push(changed);

    for changed in corpus {
        assert!(!changed.verify());
    }
}
#[test]
fn the_pd2_dual_target_is_verified_over_f2_and_f5() {
    for field in [PrimeField::new(2).unwrap(), f5()] {
        let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
        let injectives: Vec<Module> = (0..3)
            .map(|vertex| Module::injective(&algebra, vertex))
            .collect();
        let module = direct_sum(&injectives.iter().collect::<Vec<_>>()).0;
        let tilting = tilting(&module);
        assert_eq!(tilting.projective_dimension(), 2);
        let outcome = present_target(&tilting, &TargetLimits::default()).unwrap();
        let target = outcome.presented().expect("the dual target is split");
        assert_eq!(target.target().dim(), algebra.dim());
        assert!(outcome.verify());
    }
}
