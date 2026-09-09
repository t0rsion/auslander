pub(crate) fn compare_ar_sequences(
    mismatches: &mut Vec<String>,
    ctx: &str,
    theirs: &[ArEntry],
    ours: &[ArEntry],
) {
    for (their, our) in theirs.iter().zip(ours) {
        if their != our {
            mismatches.push(format!(
                "{ctx}: the almost-split sequence at {} is {:?}, ours is {:?}",
                their.module.label(),
                their.sequence,
                our.sequence
            ));
        }
    }
}

pub(crate) fn compare_irreducible_maps(
    mismatches: &mut Vec<String>,
    ctx: &str,
    theirs: &[IrrEntry],
    ours: &[IrrEntry],
) {
    for (their, our) in theirs.iter().zip(ours) {
        if their.into != our.into {
            mismatches.push(format!(
                "{ctx}: the irreducible morphisms into {} are {:?}, ours are {:?}",
                their.module.label(),
                their.into,
                our.into
            ));
        }
        if their.out_of != our.out_of {
            mismatches.push(format!(
                "{ctx}: the irreducible morphisms out of {} are {:?}, ours are {:?}",
                their.module.label(),
                their.out_of,
                our.out_of
            ));
        }
    }
}

pub(crate) fn compare_ext_algebra(
    mismatches: &mut Vec<String>,
    ctx: &str,
    theirs: &ExtAlgebra,
    ours: &ExtAlgebra,
) {
    for (label, their, our) in [
        ("ext_algebra dims", &theirs.dims, &ours.dims),
        (
            "ext_algebra min_generators",
            &theirs.min_generators,
            &ours.min_generators,
        ),
        (
            "ext_algebra product_rank",
            &theirs.product_rank,
            &ours.product_rank,
        ),
    ] {
        if their != our {
            mismatches.push(format!("{ctx}: {label} is {their:?}, ours is {our:?}"));
        }
    }
}

pub(crate) fn compare_yoneda_products(
    mismatches: &mut Vec<String>,
    ctx: &str,
    theirs: &[YonedaProduct],
    ours: &[YonedaProduct],
) {
    if theirs.len() != ours.len() {
        mismatches.push(format!(
            "{ctx}: yoneda_products has {} entries, ours has {}",
            theirs.len(),
            ours.len()
        ));
    }
    for (their, our) in theirs.iter().zip(ours) {
        if their != our {
            mismatches.push(format!(
                "{ctx}: the Yoneda product on (S_{}, S_{}, S_{}) is {their:?}, ours is {our:?}",
                their.i, their.j, their.k
            ));
        }
    }
}

pub(crate) fn compare_stable_hom(
    mismatches: &mut Vec<String>,
    ctx: &str,
    fx: &Fixture,
    ours: &Computed,
) {
    for (a, (their_row, our_row)) in fx.stable_hom.iter().zip(&ours.stable_hom).enumerate() {
        for (b, (their, our)) in their_row.iter().zip(our_row).enumerate() {
            if their != our {
                mismatches.push(format!(
                    "{ctx}: dim stable Hom({}, {}) is {their}, ours is {our}",
                    fx.designated[a].label(),
                    fx.designated[b].label()
                ));
            }
        }
    }
}

pub(crate) fn compare_ar_bool_list(
    mismatches: &mut Vec<String>,
    ctx: &str,
    label: &str,
    theirs: &[bool],
    ours: &[bool],
    designated: &[ModuleRef],
) {
    for (index, (their, our)) in theirs.iter().zip(ours).enumerate() {
        if their != our {
            mismatches.push(format!(
                "{ctx}: {} is {label} {their}, ours is {our}",
                designated[index].label()
            ));
        }
    }
}

pub(crate) fn compare_tau_periods(
    mismatches: &mut Vec<String>,
    ctx: &str,
    theirs: &[TauPeriod],
    ours: &[TauPeriod],
    designated: &[ModuleRef],
) {
    for (index, (their, our)) in theirs.iter().zip(ours).enumerate() {
        if their != our {
            mismatches.push(format!(
                "{ctx}: the tau period of {} is {their:?}, ours is {our:?}",
                designated[index].label()
            ));
        }
    }
}

/// The Auslander-Reiten layer of schema v6. Every list runs over the
/// designated modules in one fixed order, so a length difference is reported
/// once and the entrywise loops then line up.
pub(crate) fn compare_ar_layer(
    mismatches: &mut Vec<String>,
    ctx: &str,
    fx: &Fixture,
    ours: &Computed,
) {
    if fx.designated != ours.designated {
        mismatches.push(format!(
            "{ctx}: designated_modules is {:?}, ours is {:?}",
            fx.designated, ours.designated
        ));
        return;
    }
    compare_ar_sequences(mismatches, ctx, &fx.ar_sequences, &ours.ar_sequences);
    compare_irreducible_maps(
        mismatches,
        ctx,
        &fx.irreducible_maps,
        &ours.irreducible_maps,
    );
    compare_ext_algebra(mismatches, ctx, &fx.ext_algebra, &ours.ext_algebra);
    compare_yoneda_products(mismatches, ctx, &fx.yoneda_products, &ours.yoneda_products);
    compare_stable_hom(mismatches, ctx, fx, ours);
    compare_ar_bool_list(
        mismatches,
        ctx,
        "tau-rigid",
        &fx.tau_rigid,
        &ours.tau_rigid,
        &fx.designated,
    );
    compare_ar_bool_list(
        mismatches,
        ctx,
        "rigid",
        &fx.rigid,
        &ours.rigid,
        &fx.designated,
    );
    compare_tau_periods(
        mismatches,
        ctx,
        &fx.tau_period,
        &ours.tau_period,
        &fx.designated,
    );
}
