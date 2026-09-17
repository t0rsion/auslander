use super::core::CatalogAtlas;

/// A rejected catalog Ext score request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AtlasScoreError {
    /// The vector needs one entry per catalog module.
    MultiplicityLength { expected: usize, got: usize },
    /// The inclusive degree range is empty.
    DegreeRange { first: usize, last: usize },
    /// A requested degree is outside the stored table.
    DegreeOutsideAtlas { degree: usize, max_degree: usize },
    /// A checked product overflowed while scoring one matrix entry.
    ProductOverflow {
        degree: usize,
        source: usize,
        target: usize,
    },
    /// A checked sum overflowed while scoring one degree.
    SumOverflow { degree: usize },
}

display_error! { error AtlasScoreError {
    Self::MultiplicityLength { expected, got } => "multiplicity vector has {got} entries, expected {expected}";
    Self::DegreeRange { first, last } => "self-Ext degree range {first} through {last} is empty";
    Self::DegreeOutsideAtlas { degree, max_degree } => "self-Ext degree {degree} exceeds atlas bound {max_degree}";
    Self::ProductOverflow { degree, source, target } => "self-Ext score overflows at degree {degree}, pair ({source}, {target})";
    Self::SumOverflow { degree } => "self-Ext score overflows while summing degree {degree}";
} }

impl CatalogAtlas {
    /// Computes `mᵀ E_k m` for every degree in `first..=last`.
    ///
    /// `E_k[i][j]` is the stored dimension of `Ext^k(X_i, X_j)`. Every
    /// multiplication and addition uses checked `usize` arithmetic.
    pub fn self_ext_scores(
        &self,
        multiplicities: &[usize],
        first: usize,
        last: usize,
    ) -> Result<Vec<usize>, AtlasScoreError> {
        self.ext_scores(multiplicities, multiplicities, first, last)
    }

    /// Computes `mᵀ E_k n` for every degree in `first..=last`.
    pub fn ext_scores(
        &self,
        left: &[usize],
        right: &[usize],
        first: usize,
        last: usize,
    ) -> Result<Vec<usize>, AtlasScoreError> {
        self.validate_score_input(left, first, last)?;
        self.validate_score_input(right, first, last)?;
        (first..=last)
            .map(|degree| self.score_degree(left, right, degree))
            .collect()
    }

    /// Checks whether every stored bilinear term vanishes in the degree range.
    pub fn ext_vanishes(
        &self,
        left: &[usize],
        right: &[usize],
        first: usize,
        last: usize,
    ) -> Result<bool, AtlasScoreError> {
        self.validate_score_input(left, first, last)?;
        self.validate_score_input(right, first, last)?;
        Ok((first..=last).all(|degree| self.vanishes_at_degree(left, right, degree)))
    }

    /// Checks vanishing of `Ext^k(M, M)` for every degree in the range.
    pub fn self_ext_vanishes(
        &self,
        multiplicities: &[usize],
        first: usize,
        last: usize,
    ) -> Result<bool, AtlasScoreError> {
        self.ext_vanishes(multiplicities, multiplicities, first, last)
    }

    fn validate_score_input(
        &self,
        multiplicities: &[usize],
        first: usize,
        last: usize,
    ) -> Result<(), AtlasScoreError> {
        if multiplicities.len() != self.catalog().len() {
            return Err(AtlasScoreError::MultiplicityLength {
                expected: self.catalog().len(),
                got: multiplicities.len(),
            });
        }
        if first > last {
            return Err(AtlasScoreError::DegreeRange { first, last });
        }
        if last > self.max_degree() {
            return Err(AtlasScoreError::DegreeOutsideAtlas {
                degree: last,
                max_degree: self.max_degree(),
            });
        }
        Ok(())
    }

    fn score_degree(
        &self,
        lefts: &[usize],
        rights: &[usize],
        degree: usize,
    ) -> Result<usize, AtlasScoreError> {
        let mut score = 0usize;
        for (source, &left) in lefts.iter().enumerate() {
            if left == 0 {
                continue;
            }
            for (target, &right) in rights.iter().enumerate() {
                if right == 0 {
                    continue;
                }
                let term = self.score_contribution(left, right, degree, source, target)?;
                score = score
                    .checked_add(term)
                    .ok_or(AtlasScoreError::SumOverflow { degree })?;
            }
        }
        Ok(score)
    }

    fn vanishes_at_degree(&self, left: &[usize], right: &[usize], degree: usize) -> bool {
        for (source, &left_value) in left.iter().enumerate() {
            if left_value == 0 {
                continue;
            }
            for (target, &right_value) in right.iter().enumerate() {
                if right_value > 0 && self.ext_dim(source, target, degree).unwrap() > 0 {
                    return false;
                }
            }
        }
        true
    }

    fn score_contribution(
        &self,
        left: usize,
        right: usize,
        degree: usize,
        source: usize,
        target: usize,
    ) -> Result<usize, AtlasScoreError> {
        let dimension = self
            .ext_dim(source, target, degree)
            .expect("validated degree and catalog indices");
        let term = left
            .checked_mul(dimension)
            .and_then(|value| value.checked_mul(right))
            .ok_or(AtlasScoreError::ProductOverflow {
                degree,
                source,
                target,
            })?;
        Ok(term)
    }
}
