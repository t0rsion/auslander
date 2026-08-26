//! Quivers and path words.
//!
//! An arrow word is a path when consecutive arrows satisfy
//! `target(a) == source(b)`.

/// An arrow id: the position of the arrow in the list passed to [`Quiver::new`].
///
/// Stable for the lifetime of the quiver.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ArrowId(pub u32);

impl ArrowId {
    /// Position in [`Quiver::arrows`].
    #[inline]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Rejected quiver or path-word input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuiverError {
    /// Arrow `arrow` in the construction list has an endpoint outside `0..num_vertices`.
    EndpointOutOfRange {
        arrow: usize,
        vertex: u32,
        num_vertices: u32,
    },
    /// Vertex outside `0..num_vertices`.
    VertexOutOfRange { vertex: u32, num_vertices: u32 },
    /// Arrow id outside `0..num_arrows`.
    ArrowOutOfRange { arrow: ArrowId, num_arrows: usize },
    /// A path word needs at least one arrow.
    EmptyWord,
    /// `target(word[position]) != source(word[position + 1])`.
    NotComposable { position: usize },
    /// The word's stored endpoints differ from the endpoints its arrows have
    /// in the quiver it is checked against.
    EndpointsDisagree {
        stored: (u32, u32),
        computed: (u32, u32),
    },
}

display_error! { error QuiverError {
    Self::EndpointOutOfRange { arrow, vertex, num_vertices } => "arrow {arrow} has endpoint {vertex} outside 0..{num_vertices}";
    Self::VertexOutOfRange { vertex, num_vertices } => "vertex {vertex} outside 0..{num_vertices}";
    Self::ArrowOutOfRange { arrow, num_arrows } => "arrow id {} outside 0..{num_arrows}", arrow.0;
    Self::EmptyWord => "path word needs at least one arrow";
    Self::NotComposable { position } => "arrows at positions {position} and {} do not compose left to right", position + 1;
    Self::EndpointsDisagree { stored, computed } => "word stores endpoints {} -> {} but its arrows run {} -> {} in this quiver", stored.0, stored.1, computed.0, computed.1;
} }

/// A finite quiver: vertices `0..num_vertices` and a list of arrows between them.
///
/// Consecutive arrows of a path must satisfy `target(a) == source(b)`.
///
/// ```
/// use auslander::quiver::{ArrowId, Quiver};
/// let q = Quiver::new(3, &[(0, 1), (1, 2)]).unwrap();
/// assert_eq!(q.target(ArrowId(0)), q.source(ArrowId(1)));
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Quiver {
    num_vertices: u32,
    arrows: Vec<(u32, u32)>,
    arrows_from: Vec<Vec<ArrowId>>,
    arrows_to: Vec<Vec<ArrowId>>,
}

impl Quiver {
    /// Builds a quiver from `(source, target)` pairs; arrow `i` gets `ArrowId(i)`.
    ///
    /// Errors when an endpoint is outside `0..num_vertices`.
    pub fn new(num_vertices: u32, arrows: &[(u32, u32)]) -> Result<Quiver, QuiverError> {
        let n = num_vertices as usize;
        let mut arrows_from = vec![Vec::new(); n];
        let mut arrows_to = vec![Vec::new(); n];
        for (i, &(source, target)) in arrows.iter().enumerate() {
            for vertex in [source, target] {
                if vertex >= num_vertices {
                    return Err(QuiverError::EndpointOutOfRange {
                        arrow: i,
                        vertex,
                        num_vertices,
                    });
                }
            }
            let id = ArrowId(i as u32);
            arrows_from[source as usize].push(id);
            arrows_to[target as usize].push(id);
        }
        Ok(Quiver {
            num_vertices,
            arrows: arrows.to_vec(),
            arrows_from,
            arrows_to,
        })
    }

    accessor_methods! {
        /// Number of vertices; the vertices are `0..num_vertices`.
        pub num_vertices() -> u32 = |this| this.num_vertices;
        /// Number of arrows; the arrow ids are `0..num_arrows`.
        pub num_arrows() -> usize = |this| this.arrows.len();
        /// All arrows as `(source, target)` pairs, indexed by [`ArrowId::index`].
        pub arrows() -> &[(u32, u32)] = |this| &this.arrows;
        /// Source vertex of `a`. Panics if `a` is not an arrow of this quiver.
        pub source(a: ArrowId) -> u32 = |this| this.arrows[a.index()].0;
        /// Target vertex of `a`. Panics if `a` is not an arrow of this quiver.
        pub target(a: ArrowId) -> u32 = |this| this.arrows[a.index()].1;
        /// Arrows with source `v`, in increasing id order. Panics if `v >= num_vertices`.
        pub arrows_from(v: u32) -> &[ArrowId] = |this| &this.arrows_from[v as usize];
        /// Arrows with target `v`, in increasing id order. Panics if `v >= num_vertices`.
        pub arrows_to(v: u32) -> &[ArrowId] = |this| &this.arrows_to[v as usize];
    }
}

/// A path in a quiver: the trivial path `e_v` at a vertex, or a nonempty
/// composable arrow word.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PathWord {
    source: u32,
    target: u32,
    arrows: Vec<ArrowId>,
}

impl PathWord {
    /// The trivial path `e_v`. Errors if `vertex` is not in `quiver`.
    pub fn trivial(quiver: &Quiver, vertex: u32) -> Result<PathWord, QuiverError> {
        if vertex >= quiver.num_vertices() {
            return Err(QuiverError::VertexOutOfRange {
                vertex,
                num_vertices: quiver.num_vertices(),
            });
        }
        Ok(Self::trivial_unchecked(vertex))
    }

    /// The path `arrows[0]·arrows[1]·…`. Errors on an empty word, an unknown arrow id,
    /// or consecutive arrows with `target != source`.
    pub fn from_arrows(quiver: &Quiver, arrows: &[ArrowId]) -> Result<PathWord, QuiverError> {
        if arrows.is_empty() {
            return Err(QuiverError::EmptyWord);
        }
        path_endpoints(quiver, arrows)?;
        Ok(Self::from_arrows_unchecked(quiver, arrows.to_vec()))
    }

    pub(crate) fn trivial_unchecked(vertex: u32) -> PathWord {
        PathWord {
            source: vertex,
            target: vertex,
            arrows: Vec::new(),
        }
    }

    /// Caller guarantees `arrows` is nonempty, in range, and composable.
    pub(crate) fn from_arrows_unchecked(quiver: &Quiver, arrows: Vec<ArrowId>) -> PathWord {
        let source = quiver.source(arrows[0]);
        let target = quiver.target(arrows[arrows.len() - 1]);
        PathWord {
            source,
            target,
            arrows,
        }
    }

    /// Checks that this word is a path of `quiver`.
    ///
    /// Every arrow id must be in range, consecutive arrows must compose, and
    /// the stored endpoints must match the arrows' endpoints. A trivial path
    /// must name a vertex of `quiver`. A word built over `quiver` always
    /// passes. Call this on a word that may come from a different quiver.
    pub fn validate_in(&self, quiver: &Quiver) -> Result<(), QuiverError> {
        if self.arrows.is_empty() {
            if self.source >= quiver.num_vertices() {
                return Err(QuiverError::VertexOutOfRange {
                    vertex: self.source,
                    num_vertices: quiver.num_vertices(),
                });
            }
            return Ok(());
        }
        let computed = path_endpoints(quiver, &self.arrows)?;
        if (self.source, self.target) != computed {
            return Err(QuiverError::EndpointsDisagree {
                stored: (self.source, self.target),
                computed,
            });
        }
        Ok(())
    }

    accessor_methods! {
        pub source() -> u32 = |this| this.source;
        pub target() -> u32 = |this| this.target;
        /// Arrow word; empty exactly for trivial paths.
        pub arrows() -> &[ArrowId] = |this| &this.arrows;
        /// Number of arrows; 0 for trivial paths.
        #[allow(clippy::len_without_is_empty)]
        pub len() -> usize = |this| this.arrows.len();
        pub is_trivial() -> bool = |this| this.arrows.is_empty();
    }
}

fn path_endpoints(quiver: &Quiver, arrows: &[ArrowId]) -> Result<(u32, u32), QuiverError> {
    if let Some(&arrow) = arrows.iter().find(|a| a.index() >= quiver.num_arrows()) {
        return Err(QuiverError::ArrowOutOfRange {
            arrow,
            num_arrows: quiver.num_arrows(),
        });
    }
    if let Some(position) = arrows
        .windows(2)
        .position(|pair| quiver.target(pair[0]) != quiver.source(pair[1]))
    {
        return Err(QuiverError::NotComposable { position });
    }
    Ok((
        quiver.source(arrows[0]),
        quiver.target(arrows[arrows.len() - 1]),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn a3() -> Quiver {
        Quiver::new(3, &[(0, 1), (1, 2)]).unwrap()
    }

    #[test]
    fn arrows_keep_input_order_and_endpoints() {
        let q = a3();
        assert_eq!(q.num_vertices(), 3);
        assert_eq!(q.num_arrows(), 2);
        assert_eq!(q.source(ArrowId(0)), 0);
        assert_eq!(q.target(ArrowId(0)), 1);
        assert_eq!(q.arrows(), &[(0, 1), (1, 2)]);
    }

    #[test]
    fn endpoint_out_of_range_rejected() {
        assert_eq!(
            Quiver::new(2, &[(0, 2)]),
            Err(QuiverError::EndpointOutOfRange {
                arrow: 0,
                vertex: 2,
                num_vertices: 2,
            })
        );
    }

    #[test]
    fn arrows_from_and_to_list_incident_arrows() {
        let q = Quiver::new(2, &[(0, 1), (0, 1), (1, 0)]).unwrap();
        assert_eq!(q.arrows_from(0), &[ArrowId(0), ArrowId(1)]);
        assert_eq!(q.arrows_from(1), &[ArrowId(2)]);
        assert_eq!(q.arrows_to(1), &[ArrowId(0), ArrowId(1)]);
        assert_eq!(q.arrows_to(0), &[ArrowId(2)]);
    }

    #[test]
    fn trivial_path_sits_at_its_vertex() {
        let p = PathWord::trivial(&a3(), 1).unwrap();
        assert!(p.is_trivial());
        assert_eq!(p.len(), 0);
        assert_eq!((p.source(), p.target()), (1, 1));
    }

    #[test]
    fn trivial_path_rejects_unknown_vertex() {
        assert_eq!(
            PathWord::trivial(&a3(), 3),
            Err(QuiverError::VertexOutOfRange {
                vertex: 3,
                num_vertices: 3,
            })
        );
    }

    #[test]
    fn word_composes_left_to_right() {
        let p = PathWord::from_arrows(&a3(), &[ArrowId(0), ArrowId(1)]).unwrap();
        assert_eq!((p.source(), p.target()), (0, 2));
        assert_eq!(p.len(), 2);
    }

    #[test]
    fn non_composable_word_rejected() {
        assert_eq!(
            PathWord::from_arrows(&a3(), &[ArrowId(1), ArrowId(0)]),
            Err(QuiverError::NotComposable { position: 0 })
        );
    }

    #[test]
    fn empty_word_rejected() {
        assert_eq!(
            PathWord::from_arrows(&a3(), &[]),
            Err(QuiverError::EmptyWord)
        );
    }

    #[test]
    fn validate_in_accepts_words_of_the_same_quiver() {
        let q = a3();
        let p = PathWord::from_arrows(&q, &[ArrowId(0), ArrowId(1)]).unwrap();
        assert_eq!(p.validate_in(&q), Ok(()));
        let e = PathWord::trivial(&q, 2).unwrap();
        assert_eq!(e.validate_in(&q), Ok(()));
    }

    #[test]
    fn validate_in_rejects_words_from_a_different_quiver() {
        let q = a3();
        // Arrow ids exist in both quivers, but their endpoints differ.
        let other = Quiver::new(2, &[(1, 0), (0, 1)]).unwrap();
        let p = PathWord::from_arrows(&other, &[ArrowId(1), ArrowId(0)]).unwrap();
        assert_eq!(
            p.validate_in(&q),
            Err(QuiverError::NotComposable { position: 0 })
        );
        let single = PathWord::from_arrows(&other, &[ArrowId(0)]).unwrap();
        assert_eq!(
            single.validate_in(&q),
            Err(QuiverError::EndpointsDisagree {
                stored: (1, 0),
                computed: (0, 1),
            })
        );
        let big = Quiver::new(3, &[(0, 1), (1, 2), (2, 0)]).unwrap();
        let foreign = PathWord::from_arrows(&big, &[ArrowId(2)]).unwrap();
        assert_eq!(
            foreign.validate_in(&q),
            Err(QuiverError::ArrowOutOfRange {
                arrow: ArrowId(2),
                num_arrows: 2,
            })
        );
        let trivial = PathWord::trivial(&big, 2).unwrap();
        assert_eq!(trivial.validate_in(&q), Ok(()));
        let far = Quiver::new(5, &[]).unwrap();
        let outside = PathWord::trivial(&far, 4).unwrap();
        assert_eq!(
            outside.validate_in(&q),
            Err(QuiverError::VertexOutOfRange {
                vertex: 4,
                num_vertices: 3,
            })
        );
    }

    #[test]
    fn unknown_arrow_rejected() {
        assert_eq!(
            PathWord::from_arrows(&a3(), &[ArrowId(2)]),
            Err(QuiverError::ArrowOutOfRange {
                arrow: ArrowId(2),
                num_arrows: 2,
            })
        );
    }
}
