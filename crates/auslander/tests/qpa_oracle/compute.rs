/// Everything the library computes for one fixture, in the shapes the schema
/// stores.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Computed {
    pub(crate) dim: usize,
    pub(crate) cartan: Vec<Vec<usize>>,
    pub(crate) injectives: Vec<Vec<usize>>,
    pub(crate) projdim: Vec<DimOutcome>,
    pub(crate) injdim: Vec<DimOutcome>,
    pub(crate) tau: Vec<TauOutcome>,
    pub(crate) tau_injectives: Vec<TauOutcome>,
    pub(crate) decomposition: Vec<(Vec<usize>, usize)>,
    pub(crate) ext: Vec<Vec<Vec<usize>>>,
    pub(crate) designated: Vec<ModuleRef>,
    pub(crate) ar_sequences: Vec<ArEntry>,
    pub(crate) irreducible_maps: Vec<IrrEntry>,
    pub(crate) ext_algebra: ExtAlgebra,
    pub(crate) yoneda_products: Vec<YonedaProduct>,
    pub(crate) stable_hom: Vec<Vec<usize>>,
    pub(crate) tau_rigid: Vec<bool>,
    pub(crate) rigid: Vec<bool>,
    pub(crate) tau_period: Vec<TauPeriod>,
}

/// Builds the fixture's algebra from its recorded presentation, the same
/// input path QPA consumed. The documented coefficient rule applies first:
/// reduce each coefficient mod the fixture's field, drop terms that reduce to
/// zero, drop relations with no surviving terms.
pub(crate) fn build_algebra(fx: &Fixture) -> Result<Arc<Algebra>, String> {
    let field =
        PrimeField::new(fx.field).map_err(|e| format!("field {} rejected: {e}", fx.field))?;
    let arrows: Vec<(u32, u32)> = fx
        .quiver
        .arrows
        .iter()
        .map(|a| (a.source, a.target))
        .collect();
    let quiver = Quiver::new(fx.quiver.num_vertices, &arrows)
        .map_err(|e| format!("quiver rejected: {e}"))?;
    let mut relations = Vec::new();
    for (index, terms) in fx.relations.iter().enumerate() {
        let reduced: Vec<(Fp, Vec<ArrowId>)> = terms
            .iter()
            .filter_map(|term| {
                let coeff = field.elem(term.coeff);
                (!coeff.is_zero()).then(|| (coeff, term.path.iter().map(|&a| ArrowId(a)).collect()))
            })
            .collect();
        if reduced.is_empty() {
            continue;
        }
        relations.push(
            Relation::new(&quiver, field, reduced)
                .map_err(|e| format!("relation {index} rejected: {e}"))?,
        );
    }
    let presentation = Presentation::new(quiver, field, relations)
        .map_err(|e| format!("presentation rejected: {e}"))?;
    Algebra::new(presentation, &CompletionLimits::default())
        .map_err(|e| format!("algebra construction failed: {e}"))
}

pub(crate) fn dim_outcome(bounded: Bounded<usize>) -> DimOutcome {
    match bounded {
        Bounded::Exact(d) => DimOutcome::Finite(d),
        Bounded::AtLeast(d) => DimOutcome::AtLeast(d),
    }
}

/// A zero translate marks a projective input; the schema stores that as
/// `{"projective": true}` and a dimension vector otherwise.
pub(crate) fn tau_outcome(m: &Module) -> TauOutcome {
    let t = tau(m).expect("τ routes agree on fixtures");
    if t.is_zero() {
        TauOutcome::Projective
    } else {
        TauOutcome::Dimvec(t.dim_vector().to_vec())
    }
}

/// The Krull-Schmidt summands of `m` as (dimvec, multiplicity) pairs, sorted
/// lexicographically ascending with equal dimension vectors merged. An
/// undetermined decomposition is a hard failure, never an empty answer.
pub(crate) fn summand_classes(m: &Module) -> Result<Vec<(Vec<usize>, usize)>, String> {
    match krull_schmidt(m) {
        KrullSchmidtOutcome::Classes(classes) => {
            let mut counts: BTreeMap<Vec<usize>, usize> = BTreeMap::new();
            for class in classes {
                *counts
                    .entry(class.representative.dim_vector().to_vec())
                    .or_insert(0) += class.multiplicity;
            }
            Ok(counts.into_iter().collect())
        }
        KrullSchmidtOutcome::Unknown { reason } => Err(format!(
            "Krull-Schmidt decomposition undetermined: {reason}"
        )),
    }
}

/// The designated test module: the direct sum of the nonzero radicals of the
/// indecomposable projectives, decomposed by `krull_schmidt` and aggregated
/// into (dimvec, multiplicity) pairs sorted lexicographically ascending.
pub(crate) fn radical_summand_classes(
    algebra: &Arc<Algebra>,
) -> Result<Vec<(Vec<usize>, usize)>, String> {
    let n = algebra.quiver().num_vertices();
    let radicals: Vec<Module> = (0..n)
        .map(|v| radical(&Module::projective(algebra, v)).0)
        .filter(|m| !m.is_zero())
        .collect();
    if radicals.is_empty() {
        return Ok(Vec::new());
    }
    let parts: Vec<&Module> = radicals.iter().collect();
    let (total, _, _) = direct_sum(&parts);
    summand_classes(&total)
}

/// The designated modules of `algebra`, built by construction from their kind
/// and index, in the order `designated_refs` fixes.
pub(crate) fn designated_modules(algebra: &Arc<Algebra>) -> Vec<Module> {
    let n = algebra.quiver().num_vertices();
    designated_refs(n as usize)
        .into_iter()
        .map(|r| {
            let v = r.index as u32;
            match r.kind {
                ModuleKind::Simple => Module::simple(algebra, v),
                ModuleKind::Projective => Module::projective(algebra, v),
                ModuleKind::Injective => Module::injective(algebra, v),
            }
        })
        .collect()
}

/// The almost-split sequence ending at `m`, with its middle decomposed. The
/// AR duality witness is rechecked for every sequence built.
pub(crate) fn ar_sequence_of(m: &Module) -> Result<ArSequence, String> {
    let ind = IndecomposableModule::new(m)
        .map_err(|e| format!("the module is not certified indecomposable: {e}"))?;
    match almost_split(&ind).map_err(|e| format!("almost_split failed: {e}"))? {
        AlmostSplitOutcome::Projective => Ok(ArSequence::Projective),
        AlmostSplitOutcome::Sequence(built) => {
            let AlmostSplitWitness::ArDuality(witness) = built.witness() else {
                return Err("almost_split returned a non-AR-duality witness".to_string());
            };
            if !witness.verify(&ind, built.sequence(), built.chosen_ar_class()) {
                return Err("the AR duality witness does not verify".to_string());
            }
            let middle = summand_classes(built.sequence().middle())?;
            Ok(ArSequence::Sequence {
                tau: built.sequence().sub().dim_vector().to_vec(),
                middle_dimvec: built.sequence().middle().dim_vector().to_vec(),
                num_middle_summands: middle.iter().map(|(_, m)| m).sum(),
                middle,
            })
        }
    }
}

/// The irreducible morphisms into `m`, from the almost-split sequence ending
/// at `m`, or from the radical when `m` is projective. Absent exactly when
/// `m` is projective with zero radical.
pub(crate) fn irreducible_into(m: &Module, ar: &ArSequence) -> Result<IrrSide, String> {
    let endpoints = match ar {
        ArSequence::Sequence { middle, .. } => middle.clone(),
        ArSequence::Projective => {
            let rad = radical(m).0;
            if rad.is_zero() {
                return Ok(IrrSide {
                    present: false,
                    total: 0,
                    endpoints: Vec::new(),
                });
            }
            summand_classes(&rad)?
        }
    };
    let total: usize = endpoints.iter().map(|(_, v)| v).sum();
    Ok(IrrSide {
        present: total > 0,
        total,
        endpoints,
    })
}

/// The irreducible morphisms out of `m`, by duality. `D` sends the
/// irreducible morphisms out of `m` to the irreducible morphisms into `D(m)`
/// over `A^op`, and both halves of the transport are identities on the data
/// the schema stores: `opposite` keeps the vertex ids, and `dual` keeps the
/// dimension vector. So the dimension vectors computed over `A^op` compare
/// directly against the recorded targets.
///
/// The guard matches: `D(m)` is projective exactly when `m` is injective, and
/// `rad D(m)` is zero exactly when `m` equals its socle.
pub(crate) fn irreducible_out_of(m: &Module, op: &OppositeMap) -> Result<IrrSide, String> {
    let dm = dual(m, op).map_err(|e| format!("cannot dualize the module: {e}"))?;
    let ar = ar_sequence_of(&dm)?;
    let side = irreducible_into(&dm, &ar)?;
    let injective = injective_dimension(m, 0)
        .map_err(|e| format!("cannot decide injectivity: {e}"))?
        == Bounded::Exact(0);
    let is_socle = socle(m).0.dim_vector() == m.dim_vector();
    if side.present == (injective && is_socle) {
        return Err(format!(
            "the dual route reports present {}, but the module is injective {injective} \
             and equal to its socle {is_socle}",
            side.present
        ));
    }
    Ok(side)
}

/// A basis of `space` as classes, one per complement-basis coordinate.
pub(crate) fn basis_classes(space: &ExtSpace, field: PrimeField) -> Vec<ExtClass> {
    (0..space.dim())
        .map(|r| {
            let mut coords = vec![field.elem(0); space.dim()];
            coords[r] = field.elem(1);
            space
                .class_from_coordinates(&coords)
                .expect("a unit coordinate vector has the space's length and canonical entries")
        })
        .collect()
}

/// The rank over the prime field of the span of `rows` inside a space of
/// dimension `width`.
pub(crate) fn span_rank(rows: &[Vec<Fp>], width: usize, field: PrimeField) -> usize {
    if rows.is_empty() || width == 0 {
        return 0;
    }
    DenseMat::from_rows(rows).rank(&field)
}

/// The Yoneda algebra of `A/rad = sum of all simples`: the degreewise
/// dimensions, the rank of the multiplication into each degree, and the
/// minimal generators as the difference. `rad End(A/rad)` is zero, so the
/// difference is the genuine product rank.
pub(crate) fn ext_algebra_of(simples: &[Module]) -> Result<ExtAlgebra, String> {
    let parts: Vec<&Module> = simples.iter().collect();
    let (sum, _, _) = direct_sum(&parts);
    let field = sum.field();
    let spaces = (0..=MAX_EXT_DEGREE)
        .map(|k| ExtSpace::new(&sum, &sum, k))
        .collect::<Result<Vec<ExtSpace>, _>>()
        .map_err(|e| format!("cannot build Ext of the sum of simples: {e}"))?;
    let dims: Vec<usize> = spaces.iter().map(ExtSpace::dim).collect();
    let bases: Vec<Vec<ExtClass>> = spaces
        .iter()
        .map(|space| basis_classes(space, field))
        .collect();
    let mut product_rank = vec![0usize; MAX_EXT_DEGREE + 1];
    for i in 2..=MAX_EXT_DEGREE {
        let mut rows: Vec<Vec<Fp>> = Vec::new();
        for j in 1..i {
            for a in &bases[j] {
                for b in &bases[i - j] {
                    let product = a
                        .then(b)
                        .map_err(|e| format!("Yoneda product in degree {i} failed: {e}"))?;
                    if !product.space().is_compatible(&spaces[i]) {
                        return Err(format!(
                            "the degree {i} product lands in an incompatible Ext space"
                        ));
                    }
                    rows.push(product.coordinates().to_vec());
                }
            }
        }
        product_rank[i] = span_rank(&rows, dims[i], field);
    }
    let min_generators = dims
        .iter()
        .zip(&product_rank)
        .map(|(d, r)| {
            d.checked_sub(*r)
                .ok_or_else(|| format!("a product rank {r} exceeds the Ext dimension {d}"))
        })
        .collect::<Result<Vec<usize>, String>>()?;
    Ok(ExtAlgebra {
        dims,
        min_generators,
        product_rank,
    })
}

pub(crate) fn yoneda_ext1_spaces(simples: &[Module]) -> Result<Vec<Vec<ExtSpace>>, String> {
    simples
        .iter()
        .map(|source| {
            simples
                .iter()
                .map(|sink| {
                    ExtSpace::new(source, sink, 1)
                        .map_err(|e| format!("cannot build Ext^1 of two simples: {e}"))
                })
                .collect()
        })
        .collect()
}

pub(crate) fn yoneda_product_rows(
    bases: &[Vec<Vec<ExtClass>>],
    i: usize,
    j: usize,
    k: usize,
    target: &ExtSpace,
) -> Result<Vec<Vec<Fp>>, String> {
    let mut rows: Vec<Vec<Fp>> = Vec::new();
    for a in &bases[i][j] {
        for b in &bases[j][k] {
            let product = a
                .then(b)
                .map_err(|e| format!("the Yoneda product on ({i}, {j}, {k}) failed: {e}"))?;
            if !product.space().is_compatible(target) {
                return Err(format!(
                    "the product on ({i}, {j}, {k}) lands in an incompatible Ext space"
                ));
            }
            rows.push(product.coordinates().to_vec());
        }
    }
    Ok(rows)
}

pub(crate) fn yoneda_product_at(
    simples: &[Module],
    ext1: &[Vec<ExtSpace>],
    bases: &[Vec<Vec<ExtClass>>],
    field: PrimeField,
    i: usize,
    j: usize,
    k: usize,
) -> Result<YonedaProduct, String> {
    let target = ExtSpace::new(&simples[i], &simples[k], 2)
        .map_err(|e| format!("cannot build Ext^2 of two simples: {e}"))?;
    let rows = yoneda_product_rows(bases, i, j, k, &target)?;
    Ok(YonedaProduct {
        i,
        j,
        k,
        dim_ext1_ij: ext1[i][j].dim(),
        dim_ext1_jk: ext1[j][k].dim(),
        dim_ext2_ik: target.dim(),
        yoneda_map_rank: span_rank(&rows, target.dim(), field),
    })
}

/// One entry per ordered triple of simples whose two degree-one factors are
/// both nonzero, in lexicographic order, with the rank of the image of the
/// product map in `Ext^2(S_i, S_k)`.
pub(crate) fn yoneda_products_of(
    simples: &[Module],
    field: PrimeField,
) -> Result<Vec<YonedaProduct>, String> {
    let n = simples.len();
    let ext1 = yoneda_ext1_spaces(simples)?;
    let bases: Vec<Vec<Vec<ExtClass>>> = ext1
        .iter()
        .map(|row| {
            row.iter()
                .map(|space| basis_classes(space, field))
                .collect()
        })
        .collect();
    let mut out = Vec::new();
    for i in 0..n {
        for j in 0..n {
            if ext1[i][j].dim() == 0 {
                continue;
            }
            for k in 0..n {
                if ext1[j][k].dim() == 0 {
                    continue;
                }
                out.push(yoneda_product_at(simples, &ext1, &bases, field, i, j, k)?);
            }
        }
    }
    Ok(out)
}

/// The smallest `i` in `1..=bound` with `tau^i M` isomorphic to `M`, or no
/// period inside the bound. A projective module has a zero translate and is
/// never periodic. An undetermined isomorphism test is a hard failure.
///
/// The orbit runs through the Nakayama-kernel route. It is the same
/// translate, and it is the affordable one here: certified `tau` cross-checks
/// its two routes by decomposing both results, and on the deep orbit terms
/// that decomposition costs more than everything else in this harness
/// together. The first translate of every designated module still goes
/// through certified `tau`, in the tau-rigid check.
pub(crate) fn tau_period_of(m: &Module, bound: usize) -> Result<TauPeriod, String> {
    let mut current = m.clone();
    for i in 1..=bound {
        current = tau_via_nakayama_kernel(&current);
        if current.is_zero() {
            return Ok(TauPeriod::NoneUpTo(bound));
        }
        match is_isomorphic(&current, m)
            .map_err(|e| format!("the isomorphism test at step {i} failed: {e}"))?
        {
            IsoOutcome::Isomorphic(_) => return Ok(TauPeriod::Period(i)),
            IsoOutcome::NotIsomorphic(_) => {}
            IsoOutcome::Unknown { reason } => {
                return Err(format!(
                    "the isomorphism test at step {i} stayed undetermined: {reason}"
                ));
            }
        }
    }
    Ok(TauPeriod::NoneUpTo(bound))
}

pub(crate) fn compute_ext_table(simples: &[Module]) -> Vec<Vec<Vec<usize>>> {
    simples
        .iter()
        .map(|source| {
            simples
                .iter()
                .map(|sink| {
                    ext_table(source, sink, MAX_EXT_DEGREE).expect("simples share one algebra")
                })
                .collect()
        })
        .collect()
}

pub(crate) fn compute_ar_values(
    designated: &[ModuleRef],
    modules: &[Module],
    op: &OppositeMap,
) -> Result<(Vec<ArEntry>, Vec<IrrEntry>), String> {
    let mut ar_sequences = Vec::with_capacity(modules.len());
    let mut irreducible_maps = Vec::with_capacity(modules.len());
    for (reference, module) in designated.iter().zip(modules) {
        let context = |error: String| format!("{}: {error}", reference.label());
        let ar = ar_sequence_of(module).map_err(context)?;
        let into = irreducible_into(module, &ar).map_err(context)?;
        let out_of = irreducible_out_of(module, op).map_err(context)?;
        ar_sequences.push(ArEntry {
            module: *reference,
            sequence: ar,
        });
        irreducible_maps.push(IrrEntry {
            module: *reference,
            into,
            out_of,
        });
    }
    Ok((ar_sequences, irreducible_maps))
}

pub(crate) fn compute_stable_hom(modules: &[Module]) -> Result<Vec<Vec<usize>>, String> {
    modules
        .iter()
        .map(|source| {
            modules
                .iter()
                .map(|target| {
                    stable_hom_quotient(source, target)
                        .map_err(|e| format!("stable Hom failed: {e}"))
                        .map(|space| space.dim())
                })
                .collect()
        })
        .collect()
}

pub(crate) fn compute_tau_values(
    designated: &[ModuleRef],
    modules: &[Module],
    tau_period_bound: usize,
) -> Result<TauValues, String> {
    let mut tau_rigid = Vec::with_capacity(modules.len());
    let mut rigid = Vec::with_capacity(modules.len());
    let mut tau_period = Vec::with_capacity(modules.len());
    for (reference, module) in designated.iter().zip(modules) {
        let context = |error: String| format!("{}: {error}", reference.label());
        let translate = tau(module).map_err(|e| context(format!("tau failed: {e}")))?;
        let tau_rigid_value = if translate.is_zero() {
            true
        } else {
            hom_dim(module, &translate)
                .map_err(|e| context(format!("Hom(M, tau M) failed: {e}")))?
                == 0
        };
        tau_rigid.push(tau_rigid_value);
        rigid.push(
            ext_dim(module, module, 1).map_err(|e| context(format!("Ext^1(M, M) failed: {e}")))?
                == 0,
        );
        tau_period.push(tau_period_of(module, tau_period_bound).map_err(context)?);
    }
    Ok((tau_rigid, rigid, tau_period))
}

pub(crate) fn validate_ext_table(
    ext: &[Vec<Vec<usize>>],
    ext_algebra: &ExtAlgebra,
) -> Result<(), String> {
    for (degree, dimension) in ext_algebra.dims.iter().enumerate() {
        let from_table: usize = ext.iter().flatten().map(|cell| cell[degree]).sum();
        if *dimension != from_table {
            return Err(format!(
                "Ext^{degree} of the sum of simples has dimension {dimension}, \
                 but the pairwise ext table adds to {from_table}"
            ));
        }
    }
    Ok(())
}

pub(crate) fn compute(algebra: &Arc<Algebra>, tau_period_bound: usize) -> Result<Computed, String> {
    let n = algebra.quiver().num_vertices();
    let simples: Vec<Module> = (0..n).map(|v| Module::simple(algebra, v)).collect();
    let injective_modules: Vec<Module> = (0..n).map(|v| Module::injective(algebra, v)).collect();
    let ext = compute_ext_table(&simples);
    let designated = designated_refs(n as usize);
    let modules = designated_modules(algebra);
    let op = opposite(algebra).map_err(|e| format!("cannot build the opposite algebra: {e}"))?;
    let (ar_sequences, irreducible_maps) = compute_ar_values(&designated, &modules, &op)?;
    let stable = compute_stable_hom(&modules)?;
    let (tau_rigid, rigid, tau_period) =
        compute_tau_values(&designated, &modules, tau_period_bound)?;

    let ext_algebra = ext_algebra_of(&simples)?;
    validate_ext_table(&ext, &ext_algebra)?;

    Ok(Computed {
        dim: algebra.dim(),
        cartan: algebra.cartan_matrix(),
        injectives: injective_modules
            .iter()
            .map(|m| m.dim_vector().to_vec())
            .collect(),
        projdim: simples
            .iter()
            .map(|s| dim_outcome(projective_dimension(s, PROJDIM_BOUND)))
            .collect(),
        injdim: simples
            .iter()
            .map(|s| {
                dim_outcome(
                    injective_dimension(s, INJDIM_BOUND).expect("the opposite algebra builds"),
                )
            })
            .collect(),
        tau: simples.iter().map(tau_outcome).collect(),
        tau_injectives: injective_modules.iter().map(tau_outcome).collect(),
        decomposition: radical_summand_classes(algebra)?,
        ext,
        designated,
        ar_sequences,
        irreducible_maps,
        ext_algebra,
        yoneda_products: yoneda_products_of(&simples, algebra.field())?,
        stable_hom: stable,
        tau_rigid,
        rigid,
        tau_period,
    })
}
