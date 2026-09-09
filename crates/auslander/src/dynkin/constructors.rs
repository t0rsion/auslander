use crate::quiver::Quiver;

use super::types::{DynkinType, EuclideanType};

/// A quiver whose underlying graph is the named Dynkin diagram, every arrow
/// oriented away from vertex 0; `None` when the parameter names no diagram or the
/// vertex count does not fit the `u32` vertex indexing of [`Quiver`].
///
/// Vertex 0 is the center of the star: the branch vertex for `D` and `E`, and one
/// end of the path for `A`.
pub fn dynkin_quiver(dynkin: DynkinType) -> Option<Quiver> {
    u32::try_from(dynkin.num_vertices()?).ok()?;
    Some(match dynkin {
        DynkinType::A(n) => star(&[n - 1]),
        DynkinType::D(n) => star(&[1, 1, n - 3]),
        DynkinType::E6 => star(&[1, 2, 2]),
        DynkinType::E7 => star(&[1, 2, 3]),
        DynkinType::E8 => star(&[1, 2, 4]),
    })
}

/// A quiver whose underlying graph is the named Euclidean diagram; `None` when
/// the parameter names no diagram or the vertex count does not fit the `u32`
/// vertex indexing of [`Quiver`]. The cyclic cases are oriented acyclically,
/// so their path algebras are finite dimensional.
pub fn euclidean_quiver(euclidean: EuclideanType) -> Option<Quiver> {
    let vertices = u32::try_from(euclidean.num_vertices()?).ok()?;
    Some(match euclidean {
        EuclideanType::A(1) => Quiver::new(2, &[(0, 1), (0, 1)]).expect("endpoints in range"),
        EuclideanType::A(_) => {
            let n = vertices - 1;
            let mut arrows: Vec<(u32, u32)> = (0..n).map(|i| (i, i + 1)).collect();
            arrows.push((0, n));
            Quiver::new(vertices, &arrows).expect("endpoints in range")
        }
        EuclideanType::D(n) => double_fork(n - 4),
        EuclideanType::E6 => star(&[2, 2, 2]),
        EuclideanType::E7 => star(&[1, 3, 3]),
        EuclideanType::E8 => star(&[1, 2, 5]),
    })
}

/// A star quiver: a center with arms of the given lengths, every arrow
/// pointing away from the center. The caller must ensure the total vertex
/// count fits in `u32`; the internal counter does not check.
pub(crate) fn star(arms: &[usize]) -> Quiver {
    let mut arrows: Vec<(u32, u32)> = Vec::new();
    let mut next = 1u32;
    for &length in arms {
        let mut previous = 0u32;
        for _ in 0..length {
            arrows.push((previous, next));
            previous = next;
            next += 1;
        }
    }
    Quiver::new(next, &arrows).expect("star endpoints are in range")
}

/// Two leaves at each end of a path with `separation` edges; `separation = 0`
/// collapses the two ends into one vertex of degree four. The caller must
/// ensure the total vertex count `separation + 5` fits in `u32`; the internal
/// cast does not check.
pub(crate) fn double_fork(separation: usize) -> Quiver {
    let spine: Vec<u32> = (2..=2 + separation as u32).collect();
    let last = *spine.last().expect("the spine has at least one vertex");
    let mut arrows = vec![(0u32, 2u32), (1u32, 2u32)];
    for pair in spine.windows(2) {
        arrows.push((pair[0], pair[1]));
    }
    arrows.push((last, last + 1));
    arrows.push((last, last + 2));
    Quiver::new(last + 3, &arrows).expect("double fork endpoints are in range")
}
