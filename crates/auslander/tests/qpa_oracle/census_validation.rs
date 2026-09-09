fn expected_dimensions(id: &str) -> Result<[usize; 4], String> {
    match id {
        "d1111" => Ok([1, 1, 1, 1]),
        "d2112" => Ok([2, 1, 1, 2]),
        _ => Err(format!("{id}: unknown census domain")),
    }
}

fn validate_domain_identity(domain: &Domain) -> Result<(), String> {
    let expected_dimensions = expected_dimensions(&domain.id)?;
    if domain.dimensions.as_slice() != &expected_dimensions[..] {
        return Err(format!(
            "{}: dimensions do not match the census domain",
            domain.id
        ));
    }
    Ok(())
}

fn validate_domain_size(domain: &Domain) -> Result<(), String> {
    if domain.coordinate_count != coordinate_count(&domain.dimensions) {
        return Err(format!(
            "{}: coordinate count does not match its dimensions",
            domain.id
        ));
    }
    if domain.raw_space_size != u128::from(FIELD).pow(domain.coordinate_count as u32) {
        return Err(format!(
            "{}: raw space size does not match its coordinates",
            domain.id
        ));
    }
    Ok(())
}

fn validate_census_counts(domain: &Domain) -> Result<(), String> {
    if domain.candidates != domain.raw_space_size as usize
        || domain.accepted.len() != domain.accepted_modules
        || domain.rejected.len() != domain.rejected_candidates
        || domain.accepted_modules + domain.rejected_candidates != domain.candidates
    {
        return Err(format!("{}: census counts are inconsistent", domain.id));
    }
    Ok(())
}

fn validate_partition_count(domain: &Domain) -> Result<(), String> {
    if domain.accepted.len() + domain.rejected.len() != domain.candidates {
        return Err(format!("{}: raw partition is incomplete", domain.id));
    }
    Ok(())
}

fn validate_record_order(domain: &Domain) -> Result<(), String> {
    if domain
        .accepted
        .windows(2)
        .any(|pair| pair[0].cursor >= pair[1].cursor)
        || domain.rejected.windows(2).any(|pair| pair[0] >= pair[1])
    {
        return Err(format!("{}: raw records are not sorted", domain.id));
    }
    Ok(())
}

fn validate_domain_shape(domain: &Domain) -> Result<(), String> {
    validate_domain_identity(domain)?;
    validate_domain_size(domain)?;
    validate_census_counts(domain)?;
    validate_partition_count(domain)?;
    validate_record_order(domain)
}

fn validate_raw_partition(domain: &Domain) -> Result<(), String> {
    let mut accepted_index = 0;
    let mut rejected_index = 0;
    for cursor in 0..domain.raw_space_size {
        let accepted = domain
            .accepted
            .get(accepted_index)
            .map(|entry| entry.cursor)
            == Some(cursor);
        let rejected = domain.rejected.get(rejected_index) == Some(&cursor);
        if accepted == rejected {
            return Err(format!(
                "{}: raw cursor {cursor} is not partitioned",
                domain.id
            ));
        }
        if accepted {
            let entry = &domain.accepted[accepted_index];
            if entry.coordinates != digits(cursor, domain.coordinate_count)
                || entry.class >= domain.representatives.len()
            {
                return Err(format!(
                    "{}: accepted cursor {cursor} is invalid",
                    domain.id
                ));
            }
            accepted_index += 1;
        } else {
            rejected_index += 1;
        }
    }
    if accepted_index != domain.accepted.len() || rejected_index != domain.rejected.len() {
        return Err(format!(
            "{}: raw partition has an out-of-range cursor",
            domain.id
        ));
    }
    Ok(())
}

fn validate_representative_order(domain: &Domain) -> Result<(), String> {
    for (index, representative) in domain.representatives.iter().enumerate() {
        if representative.coordinates != digits(representative.cursor, domain.coordinate_count) {
            return Err(format!(
                "{}: representative {index} has wrong coordinates",
                domain.id
            ));
        }
        if index == 0 && representative.cursor != 0 {
            return Err(format!(
                "{}: first representative is not cursor zero",
                domain.id
            ));
        }
        if index > 0 && domain.representatives[index - 1].cursor >= representative.cursor {
            return Err(format!("{}: representatives are not sorted", domain.id));
        }
    }
    Ok(())
}

fn validate_representative_classes(domain: &Domain) -> Result<(), String> {
    for (index, representative) in domain.representatives.iter().enumerate() {
        let first = domain
            .accepted
            .iter()
            .find(|entry| entry.class == index)
            .ok_or_else(|| format!("{}: class {index} has no accepted cursor", domain.id))?;
        if first.cursor != representative.cursor || first.coordinates != representative.coordinates
        {
            return Err(format!(
                "{}: class {index} does not start at its representative",
                domain.id
            ));
        }
    }
    Ok(())
}

fn validate_self_ext_sets(domain: &Domain) -> Result<(), String> {
    let ext1_free = domain
        .representatives
        .iter()
        .enumerate()
        .filter_map(|(index, representative)| (representative.self_ext[1] == 0).then_some(index))
        .collect::<Vec<_>>();
    let ext1_to_3_free = domain
        .representatives
        .iter()
        .enumerate()
        .filter_map(|(index, representative)| {
            representative.self_ext[1..]
                .iter()
                .all(|&value| value == 0)
                .then_some(index)
        })
        .collect::<Vec<_>>();
    if domain.ext1_free != ext1_free || domain.ext1_to_3_free != ext1_to_3_free {
        return Err(format!(
            "{}: self-Ext index sets are inconsistent",
            domain.id
        ));
    }
    Ok(())
}

fn validate_domain(domain: &Domain) -> Result<(), String> {
    validate_domain_shape(domain)?;
    validate_raw_partition(domain)?;
    validate_representative_order(domain)?;
    validate_representative_classes(domain)?;
    validate_self_ext_sets(domain)
}

fn validate_presentation_identity(document: &Document) -> Result<(), String> {
    if document.family != FAMILY
        || document.field != FIELD
        || document.presentation_id != FAMILY
        || document.ideal_id != FAMILY
        || document.order != ORDER
    {
        return Err("root: presentation identity does not match the census fixture".to_string());
    }
    Ok(())
}

fn validate_quiver(document: &Document) -> Result<(), String> {
    if document.quiver.num_vertices != 4
        || document
            .quiver
            .arrows
            .iter()
            .map(|arrow| (arrow.source, arrow.target))
            .collect::<Vec<_>>()
            != [(0, 1), (1, 3), (0, 2), (2, 3)]
    {
        return Err("root: quiver does not match the census fixture".to_string());
    }
    Ok(())
}

fn validate_relation(document: &Document) -> Result<(), String> {
    let relation = document
        .relations
        .first()
        .ok_or_else(|| "root: relation is missing".to_string())?;
    if document.relations.len() != 1
        || relation.len() != 2
        || relation[0].coeff != 1
        || relation[0].path != [0, 1]
        || relation[1].coeff != 1
        || relation[1].path != [2, 3]
    {
        return Err("root: relation does not match the census fixture".to_string());
    }
    Ok(())
}

fn validate_domain_manifest(document: &Document) -> Result<(), String> {
    if document.domains.len() != DOMAIN_IDS.len()
        || document
            .domains
            .iter()
            .map(|domain| domain.id.as_str())
            .collect::<Vec<_>>()
            != DOMAIN_IDS
    {
        return Err("root: domain manifest does not match the census fixture".to_string());
    }
    Ok(())
}

fn validate_document(document: &Document) -> Result<(), String> {
    validate_presentation_identity(document)?;
    validate_quiver(document)?;
    validate_relation(document)?;
    validate_domain_manifest(document)
}
