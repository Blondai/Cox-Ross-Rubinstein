//! This module contains the implementation of the contingent claim trait.

use crate::{Branch, Model};

/// A trait for defining a [`ContingentClaim`].
///
/// All claims have to be of the european style.
/// Therefore, it can only be exercised at the end.
pub trait ContingentClaim {
    /// The payout of the claim.
    ///
    /// This can be based on the [`Branch`] and the underlying [`Model`].
    fn payout(&self, branch: &Branch, model: &Model) -> f64;
}
