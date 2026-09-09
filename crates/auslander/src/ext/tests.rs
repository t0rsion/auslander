use super::foundation::{
    cochain_from_coordinates, coordinates, hom_space_dim, layout, lift_through, yoneda_basis,
};
use super::*;
use crate::field::Fp;
use crate::hom::Morphism;
use crate::homspace::stack_rows;
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::resolution::{Bounded, resolve};

mod classes;
mod core;
mod products;
