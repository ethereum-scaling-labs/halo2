//! Helper for single-row double-and-add.

use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::{CurveAffine, FieldExt},
    circuit::{AssignedCell, Region},
    plonk::{
        Advice, Assigned, Column, ConstraintSystem, Constraints, Error, Expression, VirtualCells,
    },
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
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<C::Base>,
        x_a: Column<Advice>,
        x_p: Column<Advice>,
        lambda_1: Column<Advice>,
        lambda_2: Column<Advice>,
        main_selector: &dyn Fn(&mut VirtualCells<C::Base>) -> Expression<C::Base>,
    ) -> Self {
        let config = Self {
            x_a,
            x_p,
            lambda_1,
            lambda_2,
            _marker: PhantomData,
        };

        config.main_gate(meta, main_selector);

        config
    }

    /// Gate checking consistency of initial witnessed `y_a` with the first
    /// derived `y_a`.
    fn init_gate(
        &self,
        meta: &mut ConstraintSystem<C::Base>,
        selector: &dyn Fn(&mut VirtualCells<C::Base>) -> Expression<C::Base>,
        y_a_init_witnessed: &dyn Fn(&mut VirtualCells<C::Base>) -> Expression<C::Base>,
        y_a_init_derived: Rotation,
    ) {
        meta.create_gate("init check", |meta| {
            let selector = selector(meta);
            let y_a_derived = self.y_a(meta, y_a_init_derived);
            let y_a_witnessed = y_a_init_witnessed(meta);

            Constraints::with_selector(selector, Some(("init y_a", y_a_witnessed - y_a_derived)))
        });
    }

    /// Gate checking double-and-add at each step in the steady state.
    fn main_gate(
        &self,
        meta: &mut ConstraintSystem<C::Base>,
        selector: &dyn Fn(&mut VirtualCells<C::Base>) -> Expression<C::Base>,
    ) {
        meta.create_gate("main check", |meta| {
            let for_loop = |meta: &mut VirtualCells<C::Base>, y_a_next: Expression<C::Base>| {
                // x_{A,i}
                let x_a_cur = meta.query_advice(self.x_a, Rotation::cur());
                // x_{A,i-1}
                let x_a_next = meta.query_advice(self.x_a, Rotation::next());
                // λ_{2,i}
                let lambda2_cur = meta.query_advice(self.lambda_2, Rotation::cur());

                let y_a_cur = self.y_a(meta, Rotation::cur());

                // λ_{2,i}^2 − x_{A,i-1} − x_{R,i} − x_{A,i} = 0
                let secant_line = lambda2_cur.clone().square()
                    - x_a_next.clone()
                    - self.x_r(meta, Rotation::cur())
                    - x_a_cur.clone();

                // λ_{2,i}⋅(x_{A,i} − x_{A,i-1}) − y_{A,i} − y_{A,i-1} = 0
                let gradient_2 = lambda2_cur * (x_a_cur - x_a_next) - y_a_cur - y_a_next;

                std::iter::empty()
                    .chain(Some(("secant_line", secant_line)))
                    .chain(Some(("gradient_2", gradient_2)))
            };

            let selector = selector(meta);
            let y_a_next = self.y_a(meta, Rotation::next());
            Constraints::with_selector(selector, for_loop(meta, y_a_next))
        })
    }

    /// Gate checking the final output of double-and-add.
    fn final_gate(
        &self,
        meta: &mut ConstraintSystem<C::Base>,
        selector: &dyn Fn(&mut VirtualCells<C::Base>) -> Expression<C::Base>,
        y_a_final: &dyn Fn(&mut VirtualCells<C::Base>) -> Expression<C::Base>,
    ) {
        meta.create_gate("final check", |meta| {
            // x_{A,i}
            let x_a_cur = meta.query_advice(self.x_a, Rotation::cur());
            // x_{A,i-1}
            let x_a_next = meta.query_advice(self.x_a, Rotation::next());
            // λ_{2,i}
            let lambda2_cur = meta.query_advice(self.lambda_2, Rotation::cur());
            let y_a_cur = self.y_a(meta, Rotation::cur());

            let selector = selector(meta);
            let lhs = lambda2_cur * (x_a_cur - x_a_next);
            let rhs = y_a_cur + y_a_final(meta);

            Constraints::with_selector(selector, [lhs - rhs])
        })
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

    /// Derives the expression `y_a = [(lambda_1 + lambda_2) * (x_a - x_r)] / 2`.
    #[allow(non_snake_case)]
    pub(crate) fn y_a(
        &self,
        meta: &mut VirtualCells<C::Base>,
        rotation: Rotation,
    ) -> Expression<C::Base> {
        let x_a = meta.query_advice(self.x_a, rotation);
        let lambda_1 = meta.query_advice(self.lambda_1, rotation);
        let lambda_2 = meta.query_advice(self.lambda_2, rotation);
        (lambda_1 + lambda_2) * (x_a - self.x_r(meta, rotation)) * C::Base::TWO_INV
    }

    /// Assigns one double-and-add round in the steady state.
    ///
    /// The main selector must be enabled outside of this helper.
    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::type_complexity)]
    pub(crate) fn assign_region(
        &self,
        region: &mut Region<'_, C::Base>,
        offset: usize,
        (x_p, y_p): (Option<Assigned<C::Base>>, Option<Assigned<C::Base>>),
        x_a: AssignedCell<Assigned<C::Base>, C::Base>,
        y_a: Option<Assigned<C::Base>>,
    ) -> Result<
        (
            AssignedCell<Assigned<C::Base>, C::Base>,
            Option<Assigned<C::Base>>,
        ),
        Error,
    > {
        // Assign `x_p`
        region.assign_advice(|| "x_p", self.x_p, offset, || x_p.ok_or(Error::Synthesis))?;

        // Compute and assign `lambda_1`
        let lambda_1 = {
            let lambda_1 = x_a
                .value()
                .zip(y_a)
                .zip(x_p)
                .zip(y_p)
                .map(|(((x_a, y_a), x_p), y_p)| (y_a - y_p) * (*x_a - x_p).invert());

            // Assign lambda_1
            region.assign_advice(
                || "lambda_1",
                self.lambda_1,
                offset,
                || lambda_1.ok_or(Error::Synthesis),
            )?;

            lambda_1
        };

        // Compute `x_r`
        let x_r = lambda_1
            .zip(x_a.value())
            .zip(x_p)
            .map(|((lambda_1, x_a), x_p)| lambda_1.square() - *x_a - x_p);

        // Compute and assign `lambda_2`
        let lambda_2 =
            {
                let lambda_2 = x_a.value().zip(y_a).zip(x_r).zip(lambda_1).map(
                    |(((x_a, y_a), x_r), lambda_1)| {
                        y_a * C::Base::from(2) * (*x_a - x_r.evaluate()).invert() - lambda_1
                    },
                );

                region.assign_advice(
                    || "lambda_2",
                    self.lambda_2,
                    offset,
                    || lambda_2.ok_or(Error::Synthesis),
                )?;

                lambda_2
            };

        // Compute and assign `x_a` for the next row.
        let x_a_new = {
            let x_a_new = lambda_2
                .zip(x_a.value())
                .zip(x_r)
                .map(|((lambda_2, x_a), x_r)| lambda_2.square() - *x_a - x_r);

            region.assign_advice(
                || "x_a",
                self.x_a,
                offset + 1,
                || x_a_new.ok_or(Error::Synthesis),
            )?
        };

        // Compute y_a for the next row.
        let y_a_new =
            lambda_2.zip(x_a.value()).zip(x_a_new.value()).zip(y_a).map(
                |(((lambda_2, x_a), x_a_new), y_a)| lambda_2 * (*x_a - x_a_new.evaluate()) - y_a,
            );

        Ok((x_a_new, y_a_new))
    }
}
