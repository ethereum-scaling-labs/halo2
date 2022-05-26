//! Helper for single-row double-and-add.

use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::CurveAffine,
    plonk::{Advice, Column, Expression, VirtualCells},
    poly::Rotation,
};

/// A helper struct for implementing single-row double-and-add using incomplete addition.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) struct DoubleAndAdd<C: CurveAffine> {
    // x-coordinate of the accumulator in each double-and-add iteration.
    pub(crate) x_a: Column<Advice>,
    // x-coordinate of the point being added in each double-and-add iteration.
    pub(crate) x_p: Column<Advice>,
    // lambda1 in each double-and-add iteration.
    pub(crate) lambda_1: Column<Advice>,
    // lambda2 in each double-and-add iteration.
    pub(crate) lambda_2: Column<Advice>,
    _marker: PhantomData<C>,
}

impl<C: CurveAffine> DoubleAndAdd<C> {
    pub(crate) fn configure(
        x_a: Column<Advice>,
        x_p: Column<Advice>,
        lambda_1: Column<Advice>,
        lambda_2: Column<Advice>,
    ) -> Self {
        Self {
            x_a,
            x_p,
            lambda_1,
            lambda_2,
            _marker: PhantomData,
        }
    }

    /// Derives the expression `x_r = lambda_1^2 - x_a - x_p`.
    pub(crate) fn x_r(
        &self,
        meta: &mut VirtualCells<C::Base>,
        rotation: Rotation,
    ) -> Expression<C::Base> {
        let x_a = meta.query_advice(self.x_a, rotation);
        let x_p = meta.query_advice(self.x_p, rotation);
        let lambda_1 = meta.query_advice(self.lambda_1, rotation);
        lambda_1.square() - x_a - x_p
    }

    /// Derives the expression `Y_A = (lambda_1 + lambda_2) * (x_a - x_r)`.
    ///
    /// Note that this is missing the factor of `1/2`; the Sinsemilla constraints factor
    /// it out, so we leave it up to the caller to handle it.
    #[allow(non_snake_case)]
    pub(crate) fn Y_A(
        &self,
        meta: &mut VirtualCells<C::Base>,
        rotation: Rotation,
    ) -> Expression<C::Base> {
        let x_a = meta.query_advice(self.x_a, rotation);
        let lambda_1 = meta.query_advice(self.lambda_1, rotation);
        let lambda_2 = meta.query_advice(self.lambda_2, rotation);
        (lambda_1 + lambda_2) * (x_a - self.x_r(meta, rotation))
    }
}
