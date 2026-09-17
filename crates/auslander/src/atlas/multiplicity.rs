use std::ops::Deref;
use std::sync::Arc;

use crate::arquiver::IndecomposableCatalog;

use super::core::CatalogAtlas;
use super::types::{MultiplicityError, MultiplicityLimits, MultiplicityVector};

/// An exact multiplicity enumeration stopped by one of its checked limits.
#[derive(Clone, Debug)]
pub struct MultiplicityCut {
    catalog: Arc<IndecomposableCatalog>,
    target_dimensions: Vec<usize>,
    solutions: Vec<MultiplicityVector>,
    limits: MultiplicityLimits,
    reason: MultiplicityCutReason,
    nodes_visited: usize,
}

impl PartialEq for MultiplicityCut {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.catalog, &other.catalog)
            && self.target_dimensions == other.target_dimensions
            && self.solutions == other.solutions
            && self.limits == other.limits
            && self.reason == other.reason
            && self.nodes_visited == other.nodes_visited
    }
}

impl Eq for MultiplicityCut {}

/// The budget that stopped a multiplicity enumeration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MultiplicityCutReason {
    /// The next solution would exceed the retained-row ceiling.
    SolutionLimit { limit: usize },
    /// The next search state would exceed the search-node ceiling.
    NodeLimit { limit: usize },
}

display_error! { MultiplicityCutReason {
    Self::SolutionLimit { limit } => "multiplicity enumeration reached the solution limit {limit}";
    Self::NodeLimit { limit } => "multiplicity enumeration reached the search-node limit {limit}";
} }

impl MultiplicityCut {
    accessor_methods! {
        /// The complete catalog scope of the result.
        pub catalog() -> &Arc<IndecomposableCatalog> = |this| &this.catalog;
        /// The requested total dimension vector.
        pub target_dimensions() -> &[usize] = |this| &this.target_dimensions;
        /// The exact solutions found before the cut.
        pub solutions() -> &[MultiplicityVector] = |this| &this.solutions;
        /// The maximum number of retained solutions.
        pub limit() -> usize = |this| this.limits.max_solutions;
        /// The limits used by the cut computation.
        pub limits() -> MultiplicityLimits = |this| this.limits;
        /// The typed budget that stopped the search.
        pub reason() -> MultiplicityCutReason = |this| this.reason;
        /// The number of search states visited before the cut.
        pub nodes_visited() -> usize = |this| this.nodes_visited;
        /// The number of retained solutions.
        pub len() -> usize = |this| this.solutions.len();
        /// Whether the cut retained no solutions.
        pub is_empty() -> bool = |this| this.solutions.is_empty();
    }
}

/// Every multiplicity solution for one catalog and target vector.
#[derive(Clone, Debug)]
pub struct MultiplicityComplete {
    catalog: Arc<IndecomposableCatalog>,
    target_dimensions: Vec<usize>,
    solutions: Vec<MultiplicityVector>,
    limits: MultiplicityLimits,
    nodes_visited: usize,
}

impl PartialEq for MultiplicityComplete {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.catalog, &other.catalog)
            && self.target_dimensions == other.target_dimensions
            && self.solutions == other.solutions
            && self.limits == other.limits
            && self.nodes_visited == other.nodes_visited
    }
}

impl Eq for MultiplicityComplete {}

impl MultiplicityComplete {
    accessor_methods! {
        /// The complete catalog scope of the result.
        pub catalog() -> &Arc<IndecomposableCatalog> = |this| &this.catalog;
        /// The requested total dimension vector.
        pub target_dimensions() -> &[usize] = |this| &this.target_dimensions;
        /// Every solution in deterministic catalog order.
        pub solutions() -> &[MultiplicityVector] = |this| &this.solutions;
        /// The limits used by the complete computation.
        pub limits() -> MultiplicityLimits = |this| this.limits;
        /// The number of search states visited.
        pub nodes_visited() -> usize = |this| this.nodes_visited;
        /// The number of complete solutions.
        pub len() -> usize = |this| this.solutions.len();
        /// Whether the complete result has no solutions.
        pub is_empty() -> bool = |this| this.solutions.is_empty();
    }
}

impl Deref for MultiplicityComplete {
    type Target = [MultiplicityVector];

    fn deref(&self) -> &Self::Target {
        self.solutions()
    }
}

/// Complete multiplicity solutions or an exact prefix cut by a limit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MultiplicityOutcome {
    /// Every nonnegative solution of the dimension equation was enumerated.
    Complete(MultiplicityComplete),
    /// The exact lexicographic prefix reached a solution or search-node limit.
    Cut(MultiplicityCut),
}

impl MultiplicityOutcome {
    accessor_methods! {
        /// Whether the enumeration reached the complete finite solution set.
        pub is_complete() -> bool = |this| matches!(this, Self::Complete(_));
        /// The complete scoped result, or `None` after a cut.
        pub complete() -> Option<&MultiplicityComplete> = |this| match this {
            Self::Complete(result) => Some(result),
            Self::Cut(_) => None,
        };
        /// The cut prefix, or `None` for a complete result.
        pub cut() -> Option<&MultiplicityCut> = |this| match this {
            Self::Complete(_) => None,
            Self::Cut(cut) => Some(cut),
        };
        /// The catalog scope retained by the result.
        pub catalog() -> &Arc<IndecomposableCatalog> = |this| match this {
            Self::Complete(result) => result.catalog(),
            Self::Cut(result) => result.catalog(),
        };
        /// The target dimension vector retained by the result.
        pub target_dimensions() -> &[usize] = |this| match this {
            Self::Complete(result) => result.target_dimensions(),
            Self::Cut(result) => result.target_dimensions(),
        };
    }

    /// Returns the retained solutions in either outcome variant.
    pub fn solutions(&self) -> &[MultiplicityVector] {
        match self {
            Self::Complete(result) => result.solutions(),
            Self::Cut(cut) => cut.solutions(),
        }
    }

    /// Returns the number of retained solutions.
    pub fn len(&self) -> usize {
        self.solutions().len()
    }

    /// Returns whether no solution was retained.
    pub fn is_empty(&self) -> bool {
        self.solutions().is_empty()
    }
}

struct Search<'a> {
    dimensions: &'a [Vec<usize>],
    remaining: Vec<usize>,
    current: MultiplicityVector,
    solutions: Vec<MultiplicityVector>,
    limits: MultiplicityLimits,
    nodes_visited: usize,
    cut_reason: Option<MultiplicityCutReason>,
}

struct Frame {
    index: usize,
    upper: usize,
    next: usize,
    active: Option<usize>,
}

impl Search<'_> {
    fn walk(&mut self) -> Result<(), MultiplicityError> {
        let mut stack = Vec::<Frame>::new();
        stack.try_reserve(self.current.len()).map_err(|_| {
            MultiplicityError::NodeStackAllocationFailed {
                requested: self.current.len(),
            }
        })?;
        self.walk_loop(&mut stack)
    }

    fn walk_loop(&mut self, stack: &mut Vec<Frame>) -> Result<(), MultiplicityError> {
        let mut index = 0usize;
        loop {
            if self.cut_reason.is_some() {
                return Ok(());
            }
            if index == self.current.len() {
                if self.finish_leaf(stack, &mut index)? {
                    return Ok(());
                }
                continue;
            }
            if self.open_frame(index, stack)? {
                return Ok(());
            }
            if self.choose_next(index, stack) {
                index += 1;
                continue;
            }
            if self.backtrack(stack, &mut index) {
                return Ok(());
            }
        }
    }

    fn finish_leaf(
        &mut self,
        stack: &mut [Frame],
        index: &mut usize,
    ) -> Result<bool, MultiplicityError> {
        self.visit_node()?;
        if self.cut_reason.is_some() || self.commit_solution() {
            return Ok(true);
        }
        let Some(frame) = stack.last_mut() else {
            return Ok(true);
        };
        let frame_index = frame.index;
        let multiplicity = frame
            .active
            .take()
            .expect("a leaf has an active parent choice");
        self.restore(frame_index, multiplicity);
        *index = frame_index;
        Ok(false)
    }

    fn open_frame(
        &mut self,
        index: usize,
        stack: &mut Vec<Frame>,
    ) -> Result<bool, MultiplicityError> {
        if stack.last().is_some_and(|frame| frame.index == index) {
            return Ok(false);
        }
        self.visit_node()?;
        if self.cut_reason.is_some() {
            return Ok(true);
        }
        stack.push(Frame {
            index,
            upper: self.upper_bound(index),
            next: 0,
            active: None,
        });
        Ok(false)
    }

    fn choose_next(&mut self, index: usize, stack: &mut [Frame]) -> bool {
        let mut choice = None;
        while let Some(frame) = stack.last_mut() {
            if frame.next > frame.upper {
                break;
            }
            let multiplicity = frame.next;
            frame.next += 1;
            if self.fits(index, multiplicity) {
                choice = Some(multiplicity);
                break;
            }
        }
        let Some(multiplicity) = choice else {
            return false;
        };
        self.take(index, multiplicity);
        stack.last_mut().expect("the current frame exists").active = Some(multiplicity);
        true
    }

    fn backtrack(&mut self, stack: &mut Vec<Frame>, index: &mut usize) -> bool {
        stack.pop();
        let Some(parent) = stack.last_mut() else {
            return true;
        };
        let parent_index = parent.index;
        let multiplicity = parent
            .active
            .take()
            .expect("an exhausted child has an active parent choice");
        self.restore(parent_index, multiplicity);
        *index = parent_index;
        false
    }

    fn upper_bound(&self, index: usize) -> usize {
        self.dimensions[index]
            .iter()
            .zip(&self.remaining)
            .filter(|&(&dimension, _)| dimension > 0)
            .map(|(&dimension, &remaining)| remaining / dimension)
            .min()
            .unwrap_or(0)
    }

    fn fits(&self, index: usize, multiplicity: usize) -> bool {
        self.dimensions[index]
            .iter()
            .zip(&self.remaining)
            .all(|(&dimension, &remaining)| {
                dimension
                    .checked_mul(multiplicity)
                    .is_some_and(|used| used <= remaining)
            })
    }

    fn take(&mut self, index: usize, multiplicity: usize) {
        for (remaining, &dimension) in self.remaining.iter_mut().zip(&self.dimensions[index]) {
            *remaining -= dimension * multiplicity;
        }
        self.current[index] = multiplicity;
    }

    fn restore(&mut self, index: usize, multiplicity: usize) {
        for (remaining, &dimension) in self.remaining.iter_mut().zip(&self.dimensions[index]) {
            *remaining += dimension * multiplicity;
        }
        self.current[index] = 0;
    }

    fn commit_solution(&mut self) -> bool {
        if self.remaining.iter().any(|&remaining| remaining != 0) {
            return false;
        }
        if self.solutions.len() >= self.limits.max_solutions {
            self.cut_reason = Some(MultiplicityCutReason::SolutionLimit {
                limit: self.limits.max_solutions,
            });
            return true;
        }
        self.solutions.push(self.current.clone());
        false
    }

    fn visit_node(&mut self) -> Result<(), MultiplicityError> {
        if self.nodes_visited >= self.limits.max_nodes {
            self.cut_reason = Some(MultiplicityCutReason::NodeLimit {
                limit: self.limits.max_nodes,
            });
            return Ok(());
        }
        self.nodes_visited = self
            .nodes_visited
            .checked_add(1)
            .ok_or(MultiplicityError::NodeCountOverflow)?;
        Ok(())
    }
}

impl CatalogAtlas {
    /// Enumerates every multiplicity vector with the requested dimension.
    ///
    /// Entries and solutions use increasing catalog order. The result is
    /// lexicographic in that vector order. A solution-limit cut retains exactly
    /// `max_solutions` solutions when more solutions exist. `max_nodes` counts
    /// opened frames and completed leaves. The search has no cancellation
    /// control.
    pub fn enumerate_multiplicities(
        &self,
        dimensions: &[usize],
        limits: MultiplicityLimits,
    ) -> Result<MultiplicityOutcome, MultiplicityError> {
        if dimensions.len() != self.vertex_count() {
            return Err(MultiplicityError::DimensionVectorLength {
                expected: self.vertex_count(),
                got: dimensions.len(),
            });
        }
        let catalog = self.catalog().clone();
        let target_dimensions = dimensions.to_vec();
        let entry_dimensions = self.entry_dimensions();
        let mut search = Search {
            dimensions: &entry_dimensions,
            remaining: target_dimensions.clone(),
            current: vec![0; self.catalog().len()],
            solutions: Vec::new(),
            limits,
            nodes_visited: 0,
            cut_reason: None,
        };
        search.walk()?;
        if let Some(reason) = search.cut_reason {
            Ok(MultiplicityOutcome::Cut(MultiplicityCut {
                catalog,
                target_dimensions,
                solutions: search.solutions,
                limits,
                reason,
                nodes_visited: search.nodes_visited,
            }))
        } else {
            Ok(MultiplicityOutcome::Complete(MultiplicityComplete {
                catalog,
                target_dimensions,
                solutions: search.solutions,
                limits,
                nodes_visited: search.nodes_visited,
            }))
        }
    }
}
