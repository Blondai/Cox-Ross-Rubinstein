//! This module contains an assortment of basic options that can be evaluated with this lib.

use crate::{Branch, ContingentClaim, Model};

/// A macro for implementing a `new` method for initialization and a `strike` as getter method.
///
/// This should only be used for basic claims that only involve a strike as parameter.
#[macro_export]
macro_rules! impl_basic_claims {
    ($T: ty) => {
        impl $T {
            /// Initializes a new instance.
            pub fn new(strike: f64) -> Self {
                Self { strike }
            }

            /// Returns the `strike`.
            pub fn strike(&self) -> f64 {
                self.strike
            }
        }
    };
}

/// A European call option.
///
/// The payoff profile is
/// ```text
/// max(final_stock_price - strike, 0)
/// ```
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct EuropeanCall {
    strike: f64,
}

impl_basic_claims!(EuropeanCall);

impl ContingentClaim for EuropeanCall {
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let stock_price: f64 = model.stock_price(branch);

        (stock_price - self.strike).max(0_f64)
    }
}

/// A European put option.
///
/// The payoff profile is
/// ```text
/// max(strike - final_stock_price, 0)
/// ```
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct EuropeanPut {
    strike: f64,
}

impl_basic_claims!(EuropeanPut);

impl ContingentClaim for EuropeanPut {
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let stock_price: f64 = model.stock_price(branch);

        (self.strike - stock_price).max(0_f64)
    }
}

/// A European lookback call option.
///
/// The payoff profile is
/// ```text
/// max(max_stock_price - strike, 0)
/// ```
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct LookBackCall {
    strike: f64,
}

impl_basic_claims!(LookBackCall);

impl ContingentClaim for LookBackCall {
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let max_stock_price: f64 = model
            .price_history(branch)
            .iter()
            .copied()
            .reduce(f64::max)
            .unwrap(); // Safe

        (max_stock_price - self.strike).max(0_f64)
    }
}

/// A European lookback put option.
///
/// The payoff profile is
/// ```text
/// max(strike - min_stock_price, 0)
/// ```
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct LookBackPut {
    strike: f64,
}

impl_basic_claims!(LookBackPut);

impl ContingentClaim for LookBackPut {
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let min_stock_price: f64 = model
            .price_history(branch)
            .iter()
            .copied()
            .reduce(f64::min)
            .unwrap(); // Safe

        (self.strike - min_stock_price).max(0_f64)
    }
}
