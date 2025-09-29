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
            #[inline]
            pub fn new(strike: f64) -> Self {
                Self { strike }
            }

            /// Returns the `strike`.
            #[inline]
            pub fn strike(&self) -> f64 {
                self.strike
            }
        }
    };
}

/// A European Call option.
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
    #[inline]
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let stock_price: f64 = model.stock_price(branch);

        (stock_price - self.strike).max(0_f64)
    }
}

/// A European Put option.
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
    #[inline]
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let stock_price: f64 = model.stock_price(branch);

        (self.strike - stock_price).max(0_f64)
    }
}

/// A European Lookback Call option.
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

/// A European Lookback Put option.
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

/// An Asian Call option with a fixed strike.
///
/// The payoff profile is
/// ```text
/// max(average_stock_price - strike, 0)
/// ```
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct AsianCall {
    strike: f64,
}

impl_basic_claims!(AsianCall);

impl ContingentClaim for AsianCall {
    #[inline]
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let average_stock_price: f64 =
            model.price_history(branch).iter().sum::<f64>() / (model.len() as f64 + 1_f64);
        (average_stock_price - self.strike).max(0.0)
    }
}

/// An Asian Call option with a fixed strike.
///
/// The payoff profile is
/// ```text
/// max(strike - average_stock_price, 0)
/// ```
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct AsianPut {
    strike: f64,
}

impl_basic_claims!(AsianPut);

impl ContingentClaim for AsianPut {
    #[inline]
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let average_stock_price: f64 =
            model.price_history(branch).iter().sum::<f64>() / (model.len() as f64 + 1_f64);
        (self.strike - average_stock_price).max(0.0)
    }
}

/// An Asian Call option with a floating strike.
///
/// The payoff profile is
/// ```text
/// max(final_stock_price - weighting * average_stock_price, 0)
/// ```
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct AsianFloatingCall {
    weighting: f64,
}

impl AsianFloatingCall {
    /// Initializes a new instance.
    #[inline]
    pub fn new(weighting: f64) -> Self {
        Self { weighting }
    }

    /// Initializes a new instance with weighting set to one.
    #[inline]
    pub fn new_standard() -> Self {
        let weighting: f64 = 1_f64;
        Self { weighting }
    }

    /// Returns the weighting.
    #[inline]
    pub fn weighting(&self) -> f64 {
        self.weighting
    }
}

impl ContingentClaim for AsianFloatingCall {
    #[inline]
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let final_stock_price: f64 = model.stock_price(branch);
        let average_stock_price: f64 =
            model.price_history(branch).iter().sum::<f64>() / (model.len() as f64 + 1_f64);

        (final_stock_price - self.weighting * average_stock_price).max(0.0)
    }
}

/// An Asian Put option with a floating strike.
///
/// The payoff profile is
/// ```text
/// max(weighting * average_stock_price - final_stock_price, 0)
/// ```
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct AsianFloatingPut {
    weighting: f64,
}

impl AsianFloatingPut {
    /// Initializes a new instance.
    #[inline]
    pub fn new(weighting: f64) -> Self {
        Self { weighting }
    }

    /// Initializes a new instance with weighting set to one.
    #[inline]
    pub fn new_standard() -> Self {
        let weighting: f64 = 1_f64;
        Self { weighting }
    }

    /// Returns the weighting.
    #[inline]
    pub fn weighting(&self) -> f64 {
        self.weighting
    }
}

impl ContingentClaim for AsianFloatingPut {
    #[inline]
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let final_stock_price: f64 = model.stock_price(branch);
        let average_stock_price: f64 =
            model.price_history(branch).iter().sum::<f64>() / (model.len() as f64 + 1_f64);

        (self.weighting * average_stock_price - final_stock_price).max(0.0)
    }
}

/// A Cumulative Parisian Call option.
///
/// The payoff profile is
/// ```text
/// time_above * multiplier
/// ```
/// where `time_above` is the cumulative amount of periods above the strike.
///
/// This is probably not how this option works in reality.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct CumulativeParisianCall {
    strike: f64,
    multiplier: f64,
}

impl CumulativeParisianCall {
    /// Initializes a new instance.
    #[inline]
    pub fn new(strike: f64, multiplier: f64) -> Self {
        Self { strike, multiplier }
    }

    /// Returns the strike.
    #[inline]
    pub fn strike(&self) -> f64 {
        self.strike
    }

    /// Returns the multiplier.
    #[inline]
    pub fn multiplier(&self) -> f64 {
        self.multiplier
    }
}

impl ContingentClaim for CumulativeParisianCall {
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let price_history: Vec<f64> = model.price_history(branch);

        let time_above: f64 = price_history
            .iter()
            .filter(|&price| *price > self.strike)
            .count() as f64;

        time_above * self.multiplier
    }
}

/// A Cumulative Parisian Put option.
///
/// The payoff profile is
/// ```text
/// time_below * multiplier
/// ```
/// where `time_below` is the cumulative amount of periods below the strike.
///
/// This is probably not how this option works in reality.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct CumulativeParisianPut {
    strike: f64,
    multiplier: f64,
}

impl CumulativeParisianPut {
    /// Initializes a new instance.
    #[inline]
    pub fn new(strike: f64, multiplier: f64) -> Self {
        Self { strike, multiplier }
    }

    /// Returns the strike.
    #[inline]
    pub fn strike(&self) -> f64 {
        self.strike
    }

    /// Returns the multiplier.
    #[inline]
    pub fn multiplier(&self) -> f64 {
        self.multiplier
    }
}

impl ContingentClaim for CumulativeParisianPut {
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let price_history: Vec<f64> = model.price_history(branch);

        let time_below: f64 = price_history
            .iter()
            .filter(|&price| *price < self.strike)
            .count() as f64;

        time_below * self.multiplier
    }
}

/// A Binary Call Option
///
/// The payout profile is
/// ```text
/// payout * indicator(final_stock_price > strike)
/// ```
///
/// This option pays out a fixed value, when the final stock price is above the strike.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct BinaryCall {
    strike: f64,
    payout: f64,
}

impl BinaryCall {
    /// Initializes a new instance.
    #[inline]
    pub fn new(strike: f64, payout: f64) -> Self {
        Self { strike, payout }
    }

    /// Returns the strike.
    #[inline]
    pub fn strike(&self) -> f64 {
        self.strike
    }

    /// Returns the fixed payout.
    #[inline]
    pub fn payout(&self) -> f64 {
        self.payout
    }
}

impl ContingentClaim for BinaryCall {
    #[inline]
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let final_stock_price: f64 = model.stock_price(branch);

        if final_stock_price > self.strike {
            self.payout
        } else {
            0_f64
        }
    }
}

/// A Binary Put Option
///
/// The payout profile is
/// ```text
/// payout * indicator(final_stock_price < strike)
/// ```
///
/// This option pays out a fixed value, when the final stock price is below the strike.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct BinaryPut {
    strike: f64,
    payout: f64,
}

impl BinaryPut {
    /// Initializes a new instance.
    #[inline]
    pub fn new(strike: f64, payout: f64) -> Self {
        Self { strike, payout }
    }

    /// Returns the strike.
    #[inline]
    pub fn strike(&self) -> f64 {
        self.strike
    }

    /// Returns the fixed payout.
    #[inline]
    pub fn payout(&self) -> f64 {
        self.payout
    }
}

impl ContingentClaim for BinaryPut {
    #[inline]
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let final_stock_price: f64 = model.stock_price(branch);

        if final_stock_price < self.strike {
            self.payout
        } else {
            0_f64
        }
    }
}

/// A Binary Asian Call Option
///
/// The payout profile is
/// ```text
/// payout * indicator(average_stock_price > strike)
/// ```
///
/// This option pays out a fixed value, when the average stock price is above the strike.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct BinaryAsianCall {
    strike: f64,
    payout: f64,
}

impl BinaryAsianCall {
    /// Initializes a new instance.
    #[inline]
    pub fn new(strike: f64, payout: f64) -> Self {
        Self { strike, payout }
    }

    /// Returns the strike.
    #[inline]
    pub fn strike(&self) -> f64 {
        self.strike
    }

    /// Returns the fixed payout.
    #[inline]
    pub fn payout(&self) -> f64 {
        self.payout
    }
}

impl ContingentClaim for BinaryAsianCall {
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let average_stock_price: f64 =
            model.price_history(branch).iter().sum() / (model.len() as f64 + 1_f64);

        if average_stock_price > self.strike {
            self.payout
        } else {
            0_f64
        }
    }
}

/// A Binary Asian Put Option
///
/// The payout profile is
/// ```text
/// payout * indicator(average_stock_price < strike)
/// ```
///
/// This option pays out a fixed value, when the average stock price is above the strike.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct BinaryAsianPut {
    strike: f64,
    payout: f64,
}

impl BinaryAsianPut {
    /// Initializes a new instance.
    #[inline]
    pub fn new(strike: f64, payout: f64) -> Self {
        Self { strike, payout }
    }

    /// Returns the strike.
    #[inline]
    pub fn strike(&self) -> f64 {
        self.strike
    }

    /// Returns the fixed payout.
    #[inline]
    pub fn payout(&self) -> f64 {
        self.payout
    }
}

impl ContingentClaim for BinaryAsianPut {
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let average_stock_price: f64 =
            model.price_history(branch).iter().sum() / (model.len() as f64 + 1_f64);

        if average_stock_price < self.strike {
            self.payout
        } else {
            0_f64
        }
    }
}

/// A Binary Lookback Call Option
///
/// The payout profile is
/// ```text
/// payout * indicator(max_stock_price > strike)
/// ```
///
/// This option pays out a fixed value, when the max stock price is above the strike.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct BinaryLookBackCall {
    strike: f64,
    payout: f64,
}

impl BinaryLookBackCall {
    /// Initializes a new instance.
    #[inline]
    pub fn new(strike: f64, payout: f64) -> Self {
        Self { strike, payout }
    }

    /// Returns the strike.
    #[inline]
    pub fn strike(&self) -> f64 {
        self.strike
    }

    /// Returns the fixed payout.
    #[inline]
    pub fn payout(&self) -> f64 {
        self.payout
    }
}

impl ContingentClaim for BinaryLookBackCall {
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let max_stock_price: f64 = model
            .price_history(branch)
            .iter()
            .copied()
            .reduce(f64::max)
            .unwrap();

        if max_stock_price > self.strike {
            self.payout
        } else {
            0_f64
        }
    }
}

/// A Binary Lookback Put Option
///
/// The payout profile is
/// ```text
/// payout * indicator(max_stock_price > strike)
/// ```
///
/// This option pays out a fixed value, when the max stock price is above the strike.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct BinaryLookBackPut {
    strike: f64,
    payout: f64,
}

impl BinaryLookBackPut {
    /// Initializes a new instance.
    #[inline]
    pub fn new(strike: f64, payout: f64) -> Self {
        Self { strike, payout }
    }

    /// Returns the strike.
    #[inline]
    pub fn strike(&self) -> f64 {
        self.strike
    }

    /// Returns the fixed payout.
    #[inline]
    pub fn payout(&self) -> f64 {
        self.payout
    }
}

impl ContingentClaim for BinaryLookBackPut {
    fn payout(&self, branch: &Branch, model: &Model) -> f64 {
        let min_stock_price: f64 = model
            .price_history(branch)
            .iter()
            .copied()
            .reduce(f64::min)
            .unwrap();

        if min_stock_price < self.strike {
            self.payout
        } else {
            0_f64
        }
    }
}
