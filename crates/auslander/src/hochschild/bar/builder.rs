use std::sync::Arc;

use crate::algebra::Algebra;
use crate::field::PrimeField;
use crate::linalg::DenseMat;

use super::super::cochain::{check_square, coboundaries, cocycles, complement, next_usize};
use super::super::limits::BarStage;
use super::super::outcome::{DegreeInner, HochschildDegree};
use super::{BuildResult, InnerResult, Layout, Ledger, Shape, TupleOffsets, differential, shape};

struct DegreePreparation {
    current_shape: Shape,
    next_power: Vec<Vec<usize>>,
    next_shape: Shape,
    current_layout: Layout,
    next_offsets: TupleOffsets,
}

pub(super) struct DegreeBuilder<'a> {
    algebra: &'a Arc<Algebra>,
    field: PrimeField,
    ledger: &'a mut Ledger,
    current: Option<Vec<Vec<usize>>>,
    shape: Option<Shape>,
    offsets: Option<TupleOffsets>,
    starts: Vec<Vec<usize>>,
    previous: Option<HochschildDegree>,
}

impl<'a> DegreeBuilder<'a> {
    pub(super) fn new(algebra: &'a Arc<Algebra>, ledger: &'a mut Ledger) -> Self {
        Self {
            algebra,
            field: algebra.field(),
            ledger,
            current: None,
            shape: None,
            offsets: None,
            starts: Vec::new(),
            previous: None,
        }
    }

    pub(super) fn run(mut self, max_degree: usize) -> InnerResult<()> {
        for degree in 0..=max_degree {
            self.ledger.work(degree, BarStage::DegreeRecord, 1)?;
            let degree_value = self.degree(degree)?;
            self.ledger.degrees.push(degree_value.clone());
            self.ledger.completed_degree_count += 1;
            self.previous = Some(degree_value);
        }
        Ok(())
    }

    fn degree(&mut self, degree: usize) -> InnerResult<HochschildDegree> {
        let preparation = self.prepare(degree)?;
        let spaces = self.spaces(degree, &preparation)?;
        let value = HochschildDegree(Arc::new(DegreeInner {
            algebra: self.algebra.clone(),
            degree,
            limits: self.ledger.limits,
            layout: preparation.current_layout,
            differential: spaces.0,
            cocycles: spaces.1,
            coboundaries: spaces.2,
            complement: spaces.3,
        }));
        self.current = Some(preparation.next_power);
        self.shape = Some(preparation.next_shape);
        self.offsets = Some(preparation.next_offsets);
        Ok(value)
    }

    fn prepare(&mut self, degree: usize) -> InnerResult<DegreePreparation> {
        let current_shape = self.current_shape(degree)?;
        let (next_degree, next_power, next_shape) = self.next_shape(degree, &current_shape)?;
        let current_offsets = self.offsets.take().map(Ok).unwrap_or_else(|| {
            shape::build_tuple_offsets(
                self.algebra,
                degree,
                &current_shape,
                &self.starts,
                self.ledger,
            )
        })?;
        let current_layout = shape::build_layout(self.algebra, &current_shape, current_offsets);
        let next_offsets = shape::build_tuple_offsets(
            self.algebra,
            next_degree,
            &next_shape,
            &self.starts,
            self.ledger,
        )?;
        Ok(DegreePreparation {
            current_shape,
            next_power,
            next_shape,
            current_layout,
            next_offsets,
        })
    }

    fn current_shape(&mut self, degree: usize) -> InnerResult<Shape> {
        let mut shape = match self.shape.take() {
            Some(shape) => shape,
            None => shape::measure_identity_shape(self.algebra, self.ledger, degree)?,
        };
        if degree == 0 {
            self.starts.push(std::mem::take(&mut shape.starts));
        }
        Ok(shape)
    }

    fn next_shape(
        &mut self,
        degree: usize,
        current_shape: &Shape,
    ) -> InnerResult<(usize, Vec<Vec<usize>>, Shape)> {
        let next_degree = next_usize(self.ledger, degree, BarStage::Shape, degree)?;
        let next_power =
            shape::advance_power(self.current.as_deref(), self.algebra, self.ledger, degree)?;
        let mut next_shape = shape::measure_shape(self.algebra, &next_power, self.ledger, degree)?;
        self.starts.push(std::mem::take(&mut next_shape.starts));
        shape::reserve_layout_work(current_shape, &next_shape, degree, self.ledger)?;
        Ok((next_degree, next_power, next_shape))
    }

    fn spaces(
        &mut self,
        degree: usize,
        preparation: &DegreePreparation,
    ) -> InnerResult<(DenseMat, DenseMat, DenseMat, DenseMat)> {
        let differential = differential::build_differential(
            self.algebra,
            degree,
            &preparation.current_shape,
            &preparation.current_layout,
            &preparation.next_offsets.offsets,
            &self.starts,
            self.ledger,
        )?;
        if let Some(previous) = &self.previous {
            check_square(
                &previous.0.differential,
                &differential,
                &self.field,
                degree,
                self.ledger,
            )?;
        }
        let cocycles = cocycles(&differential, &self.field, degree, self.ledger)?;
        let coboundaries = self.coboundaries(degree, preparation.current_shape.cochain_dim)?;
        let complement = complement(&cocycles, &coboundaries, &self.field, degree, self.ledger)?;
        Ok((differential, cocycles, coboundaries, complement))
    }

    fn coboundaries(&mut self, degree: usize, cochain_dim: usize) -> BuildResult<DenseMat> {
        match &self.previous {
            Some(previous) => {
                coboundaries(&previous.0.differential, &self.field, degree, self.ledger)
            }
            None => Ok(DenseMat::zero(0, cochain_dim)),
        }
    }
}
