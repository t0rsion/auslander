/// A simply laced Dynkin diagram.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DynkinType {
    /// The path on `n` vertices, `n ≥ 1`.
    A(usize),
    /// The tree with one vertex of degree three whose three arms have lengths
    /// `1, 1, n - 3`, so `n` vertices in all, `n ≥ 4`.
    D(usize),
    /// The tree with one vertex of degree three whose arms have lengths
    /// `1, 2, 2`.
    E6,
    /// The tree with one vertex of degree three whose arms have lengths
    /// `1, 2, 3`.
    E7,
    /// The tree with one vertex of degree three whose arms have lengths
    /// `1, 2, 4`.
    E8,
}

impl DynkinType {
    /// The number of vertices of the diagram, or `None` when the parameter
    /// names no Dynkin diagram (`A(n)` needs `n ≥ 1`, `D(n)` needs `n ≥ 4`).
    pub fn num_vertices(self) -> Option<usize> {
        match self {
            Self::A(n) => (n >= 1).then_some(n),
            Self::D(n) => (n >= 4).then_some(n),
            Self::E6 => Some(6),
            Self::E7 => Some(7),
            Self::E8 => Some(8),
        }
    }

    /// The number of positive roots, equal by Gabriel's theorem to the number
    /// of isomorphism classes of indecomposable representations of any quiver
    /// with this underlying graph, or `None` when the parameter names no
    /// Dynkin diagram or the count does not fit in a `usize`.
    pub fn indecomposable_count(self) -> Option<usize> {
        match self {
            // Halve the even factor before multiplying: n(n+1)/2 is often
            // representable when n(n+1) is not.
            Self::A(n) => (n >= 1)
                .then(|| {
                    if n % 2 == 0 {
                        (n / 2).checked_mul(n.checked_add(1)?)
                    } else {
                        n.checked_mul(n / 2 + 1)
                    }
                })
                .flatten(),
            Self::D(n) => (n >= 4).then(|| n.checked_mul(n - 1)).flatten(),
            Self::E6 => Some(36),
            Self::E7 => Some(63),
            Self::E8 => Some(120),
        }
    }
}

display_error! { DynkinType {
    Self::A(n) => "A_{n}";
    Self::D(n) => "D_{n}";
    Self::E6 => "E_6";
    Self::E7 => "E_7";
    Self::E8 => "E_8";
} }

/// A simply laced Euclidean (affine) diagram. The subscript is the rank of the
/// finite diagram it extends, so the diagram itself has one more vertex.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EuclideanType {
    /// Two vertices joined by a double edge when `n = 1`, the cycle on
    /// `n + 1` vertices when `n ≥ 2`.
    A(usize),
    /// The tree on `n + 1` vertices with two leaves at each end of a path of
    /// `n - 3` vertices, `n ≥ 4`; for `n = 4` the path is a single vertex of
    /// degree four.
    D(usize),
    /// The tree with one vertex of degree three whose arms have lengths
    /// `2, 2, 2`.
    E6,
    /// The tree with one vertex of degree three whose arms have lengths
    /// `1, 3, 3`.
    E7,
    /// The tree with one vertex of degree three whose arms have lengths
    /// `1, 2, 5`.
    E8,
}

impl EuclideanType {
    /// The number of vertices of the diagram, or `None` when the parameter
    /// names no Euclidean diagram (`A(n)` needs `n ≥ 1`, `D(n)` needs
    /// `n ≥ 4`) or the count does not fit in a `usize`.
    pub fn num_vertices(self) -> Option<usize> {
        match self {
            Self::A(n) => (n >= 1).then(|| n.checked_add(1)).flatten(),
            Self::D(n) => (n >= 4).then(|| n.checked_add(1)).flatten(),
            Self::E6 => Some(7),
            Self::E7 => Some(8),
            Self::E8 => Some(9),
        }
    }
}

display_error! { EuclideanType {
    Self::A(n) => "affine A_{n}";
    Self::D(n) => "affine D_{n}";
    Self::E6 => "affine E_6";
    Self::E7 => "affine E_7";
    Self::E8 => "affine E_8";
} }
