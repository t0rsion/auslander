use super::portable::{
    build_chunk, chunk_source_count, primitive_work_units, source_count, validate_config,
};
use super::portable_types::{
    HomologicalStreamBudget, HomologicalStreamPortableError, HomologicalStreamPortableStatus,
    HomologicalStreamVerifyLimits, VerifiedHomologicalStream,
};
use super::{
    HomologicalBatchStreamChunk, HomologicalBatchStreamWork, HomologicalSelfPairCheckpointStream,
    HomologicalStreamCutReason, HomologicalStreamPortable,
};
use crate::census::{CensusOutcome, CensusPortable, CensusPortableStatus};

pub(super) fn verify_portable(
    portable: &HomologicalStreamPortable,
    limits: HomologicalStreamVerifyLimits,
) -> Result<VerifiedHomologicalStream, HomologicalStreamPortableError> {
    check_limits(portable, limits)?;
    if !portable.has_valid_fingerprint() {
        return Err(HomologicalStreamPortableError::FingerprintMismatch);
    }
    let census = CensusPortable::from_json(portable.census(), limits.census.parse)?;
    if census.fingerprint() != portable.census_fingerprint() {
        return Err(HomologicalStreamPortableError::CensusFingerprintMismatch);
    }
    if !matches!(census.status(), CensusPortableStatus::Complete) {
        return Err(HomologicalStreamPortableError::CensusNotComplete);
    }
    let verified_census = census.verify(limits.census)?;
    if !matches!(verified_census.outcome(), CensusOutcome::Complete(_)) {
        return Err(HomologicalStreamPortableError::CensusNotComplete);
    }
    verify_prefix(portable, &verified_census)?;
    Ok(VerifiedHomologicalStream {
        portable: portable.clone(),
        census: verified_census,
    })
}

impl VerifiedHomologicalStream {
    /// Resumes from the next unverified representative without recomputing stored rows.
    pub fn resume(
        &self,
        budget: HomologicalStreamBudget,
        control: Option<&crate::control::ComputationControl>,
    ) -> Result<HomologicalSelfPairCheckpointStream, HomologicalStreamPortableError> {
        if matches!(
            self.portable().status(),
            HomologicalStreamPortableStatus::Complete
        ) {
            return Err(HomologicalStreamPortableError::CountMismatch {
                field: "complete checkpoint cannot resume".to_string(),
            });
        }
        HomologicalSelfPairCheckpointStream::from_verified_checkpoint(self, budget, control)
    }
}

fn check_limits(
    portable: &HomologicalStreamPortable,
    limits: HomologicalStreamVerifyLimits,
) -> Result<(), HomologicalStreamPortableError> {
    let max_representatives = limits.max_representatives as u64;
    check_limit(
        "max_degree",
        portable.max_degree() as u64,
        limits.max_degree as u64,
    )?;
    check_limit(
        "rows",
        portable.rows().len() as u64,
        limits.parse.max_rows as u64,
    )?;
    check_limit(
        "next_source",
        portable.next_source() as u64,
        max_representatives,
    )?;
    check_limit("work.sources", portable.work().sources, max_representatives)?;
    let work_units = primitive_work_units(portable.work())?;
    check_limit("work_units", work_units, limits.max_work_units)?;
    validate_config(portable.max_degree(), portable.config().chunk_limits)
}

fn check_limit(
    field: &'static str,
    declared: u64,
    limit: u64,
) -> Result<(), HomologicalStreamPortableError> {
    if declared > limit {
        Err(HomologicalStreamPortableError::VerificationLimit {
            field,
            declared,
            limit,
        })
    } else {
        Ok(())
    }
}

fn verify_prefix(
    portable: &HomologicalStreamPortable,
    census: &crate::census::VerifiedCensus,
) -> Result<(), HomologicalStreamPortableError> {
    let total = source_count(census);
    let next = portable.next_source();
    if next > total {
        return Err(HomologicalStreamPortableError::DomainMismatch {
            field: "next_source exceeds representative catalog".to_string(),
        });
    }
    if portable.rows().len() != next {
        return Err(HomologicalStreamPortableError::CountMismatch {
            field: "rows and next_source".to_string(),
        });
    }
    if portable.work().sources != next as u64 {
        return Err(HomologicalStreamPortableError::CountMismatch {
            field: "work.sources".to_string(),
        });
    }
    let degree_steps = portable
        .max_degree()
        .checked_add(1)
        .expect("verification validates degree overflow");
    let capacity = portable.config().chunk_limits.capacity(degree_steps);
    verify_chunk_sizes(portable, capacity)?;
    let mut rebuilt_work = HomologicalBatchStreamWork::default();
    let mut first = 0usize;
    for count in portable.chunk_sizes().iter().copied() {
        let chunk = build_chunk(
            census,
            first,
            count,
            portable.max_degree(),
            portable.config().chunk_limits,
        )?;
        compare_chunk(portable, &chunk, first)?;
        rebuilt_work.add_chunk(chunk.work(), count)?;
        first += count;
    }
    if rebuilt_work != portable.work() {
        return Err(HomologicalStreamPortableError::ReplayMismatch {
            field: "work".to_string(),
        });
    }
    verify_status(portable, census, rebuilt_work)
}

fn verify_chunk_sizes(
    portable: &HomologicalStreamPortable,
    capacity: u64,
) -> Result<(), HomologicalStreamPortableError> {
    let next = portable.next_source();
    if portable.chunk_sizes().len() as u64 != portable.work().chunks {
        return Err(HomologicalStreamPortableError::CountMismatch {
            field: "chunk sizes and work.chunks".to_string(),
        });
    }
    let mut covered = 0usize;
    for (index, size) in portable.chunk_sizes().iter().copied().enumerate() {
        if size == 0 {
            return Err(HomologicalStreamPortableError::CountMismatch {
                field: format!("chunk size {index} is zero"),
            });
        }
        if size as u64 > capacity {
            return Err(HomologicalStreamPortableError::CountMismatch {
                field: format!("chunk size {index} exceeds capacity"),
            });
        }
        if size > next - covered {
            return Err(HomologicalStreamPortableError::CountMismatch {
                field: "chunk sizes exceed next_source".to_string(),
            });
        }
        covered += size;
    }
    if covered != next {
        return Err(HomologicalStreamPortableError::CountMismatch {
            field: "chunk sizes and next_source".to_string(),
        });
    }
    Ok(())
}

fn compare_chunk(
    portable: &HomologicalStreamPortable,
    chunk: &HomologicalBatchStreamChunk,
    first: usize,
) -> Result<(), HomologicalStreamPortableError> {
    let end = first
        .checked_add(chunk.rows().len())
        .ok_or(HomologicalStreamPortableError::CounterOverflow { field: "row range" })?;
    if portable.rows().get(first..end) != Some(chunk.rows()) {
        return Err(HomologicalStreamPortableError::ReplayMismatch {
            field: format!("rows {first}..{end}"),
        });
    }
    if !chunk.verify() {
        return Err(HomologicalStreamPortableError::ReplayMismatch {
            field: format!("chunk {first}"),
        });
    }
    Ok(())
}

fn verify_status(
    portable: &HomologicalStreamPortable,
    census: &crate::census::VerifiedCensus,
    work: HomologicalBatchStreamWork,
) -> Result<(), HomologicalStreamPortableError> {
    let next = portable.next_source();
    let total = source_count(census);
    match portable.status() {
        HomologicalStreamPortableStatus::Complete => verify_complete(next, total),
        HomologicalStreamPortableStatus::Active => verify_active(portable, next, total, work),
        HomologicalStreamPortableStatus::Cut(reason) => {
            verify_cut(portable, census, next, total, work, *reason)
        }
    }
}

fn verify_complete(next: usize, total: usize) -> Result<(), HomologicalStreamPortableError> {
    if next == total {
        Ok(())
    } else {
        Err(HomologicalStreamPortableError::CountMismatch {
            field: "complete status".to_string(),
        })
    }
}

fn verify_active(
    portable: &HomologicalStreamPortable,
    next: usize,
    total: usize,
    work: HomologicalBatchStreamWork,
) -> Result<(), HomologicalStreamPortableError> {
    if next >= total {
        return Err(HomologicalStreamPortableError::CountMismatch {
            field: "active status".to_string(),
        });
    }
    let units = primitive_work_units(work)?;
    let budget = portable.config().budget;
    if next == 0 || ((next as u64) < budget.max_sources && units < budget.max_work_units) {
        Ok(())
    } else {
        Err(HomologicalStreamPortableError::CountMismatch {
            field: "active status at a budget boundary".to_string(),
        })
    }
}

fn verify_cut(
    portable: &HomologicalStreamPortable,
    census: &crate::census::VerifiedCensus,
    next: usize,
    total: usize,
    work: HomologicalBatchStreamWork,
    reason: HomologicalStreamCutReason,
) -> Result<(), HomologicalStreamPortableError> {
    let budget = portable.config().budget;
    match reason {
        HomologicalStreamCutReason::Cancelled => verify_cancelled(next, total),
        HomologicalStreamCutReason::SourceLimit { limit } => {
            if limit != budget.max_sources {
                return Err(HomologicalStreamPortableError::CountMismatch {
                    field: "source-limit reason and budget".to_string(),
                });
            }
            verify_source_limit(next, total, limit)
        }
        HomologicalStreamCutReason::WorkLimit { limit } => {
            if limit != budget.max_work_units {
                return Err(HomologicalStreamPortableError::CountMismatch {
                    field: "work-limit reason and budget".to_string(),
                });
            }
            verify_work_boundary(portable, census, work, limit)
        }
    }
}

fn verify_cancelled(next: usize, total: usize) -> Result<(), HomologicalStreamPortableError> {
    if next < total {
        Ok(())
    } else {
        Err(HomologicalStreamPortableError::CountMismatch {
            field: "cancelled complete prefix".to_string(),
        })
    }
}

fn verify_source_limit(
    next: usize,
    total: usize,
    limit: u64,
) -> Result<(), HomologicalStreamPortableError> {
    if next as u64 == limit && next < total {
        Ok(())
    } else {
        Err(HomologicalStreamPortableError::CountMismatch {
            field: "source-limit boundary".to_string(),
        })
    }
}

fn verify_work_boundary(
    portable: &HomologicalStreamPortable,
    census: &crate::census::VerifiedCensus,
    work: HomologicalBatchStreamWork,
    limit: u64,
) -> Result<(), HomologicalStreamPortableError> {
    let next = portable.next_source();
    let total = source_count(census);
    let max_sources = portable.config().budget.max_sources;
    let units = primitive_work_units(work)?;
    if next >= total {
        return Err(HomologicalStreamPortableError::CountMismatch {
            field: "work-limit complete prefix".to_string(),
        });
    }
    if units > limit {
        return Err(HomologicalStreamPortableError::CountMismatch {
            field: "work-limit committed work".to_string(),
        });
    }
    if next as u64 >= max_sources {
        return Err(HomologicalStreamPortableError::CountMismatch {
            field: "work-limit source boundary".to_string(),
        });
    }
    if units == limit {
        return Ok(());
    }
    let count = chunk_source_count(portable, total);
    let chunk = build_chunk(
        census,
        next,
        count,
        portable.max_degree(),
        portable.config().chunk_limits,
    )?;
    let mut next_work = work;
    next_work.add_chunk(chunk.work(), count)?;
    if primitive_work_units(next_work)? > limit {
        Ok(())
    } else {
        Err(HomologicalStreamPortableError::CountMismatch {
            field: "work-limit boundary".to_string(),
        })
    }
}
