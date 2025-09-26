//! This module contains the implementations of the model struct.

use std::fmt;

use crate::{
    Branch, BranchGenerator, ContingentClaim,
    Tick::{Down, Up},
};

/// This represents the parameters of the model.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Model {
    /// The initial price of the stock.
    initial_stock_price: f64,

    /// The amount of the periods.
    periods: usize,

    /// The [`Down`] factor for the stock price.
    down_factor: f64,

    /// The risk-free factor.
    ///
    /// This is 1 plus the risk-free interest rate.
    risk_free_factor: f64,

    /// The [`Up`] factor for the stock price.
    up_factor: f64,

    /// The risk-free probability of [`Up`].
    ///
    /// ```text
    /// (risk_free_factor - down_factor) / (up_factor - down_factor)
    /// ```
    up_prob: f64,

    /// The risk-free probability of [`Down`].
    ///
    /// ```text
    /// 1 - up_prob
    /// ```
    down_prob: f64,
}

impl Model {
    /// Creates a new [`Model`] instance.
    ///
    /// # Arguments
    ///
    /// * `initial_price`: The initial price of the stock.
    /// * `periods`: The amount of the periods.
    /// * `down_factor`: The [`Down`] factor for the stock price.
    /// * `risk_free_factor`: One plus the risk-free interest rate.
    /// * `up_factor`: The [`Up`] factor for the stock price.
    ///
    /// # Returns
    ///
    /// * [`Model`]: down_factor < risk_free_factor < up_factor.
    /// * [`ModelError::AllowsArbitrage`]: Other wise.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Model, ModelError};
    /// let model: Result<Model, ModelError> = Model::new(100_f64, 2, 0.5, 1.0, 2.0);
    /// assert_eq!(model.is_ok(), true);
    /// // Allows arbitrage
    /// let allows_arbitrage: Result<Model, ModelError> = Model::new(100_f64, 2, 1.5, 1.0, 2.0);
    /// assert_eq!(allows_arbitrage.is_err(), true);
    /// ```
    #[inline]
    pub fn new(
        initial_stock_price: f64,
        periods: usize,
        down_factor: f64,
        risk_free_factor: f64,
        up_factor: f64,
    ) -> Result<Model, ModelError> {
        ModelError::check_arbitrage(down_factor, risk_free_factor, up_factor)?;

        let up_prob: f64 = (risk_free_factor - down_factor) / (up_factor - down_factor);
        let down_prob: f64 = 1_f64 - up_prob;

        Ok(Model {
            initial_stock_price,
            periods,
            down_factor,
            risk_free_factor,
            up_factor,
            up_prob,
            down_prob,
        })
    }

    /// Returns the amount of periods in the [`Model`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Model, ModelError};
    /// let model: Model = Model::new(100_f64, 2, 0.5, 1.0, 2.0).unwrap();
    /// assert_eq!(model.len(), 2);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.periods
    }

    /// Returns the initial stock price in the [`Model`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Model, ModelError};
    /// let model: Model = Model::new(100_f64, 2, 0.5, 1.0, 2.0).unwrap();
    /// assert_eq!(model.initial_stock_price(), 100_f64);
    /// ```
    #[inline]
    pub fn initial_stock_price(&self) -> f64 {
        self.initial_stock_price
    }

    /// Returns the [`Down`] factor of the [`Model`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Model, ModelError};
    /// let model: Model = Model::new(100_f64, 2, 0.5, 1.0, 2.0).unwrap();
    /// assert_eq!(model.down_factor(), 0.5);
    /// ```
    #[inline]
    pub fn down_factor(&self) -> f64 {
        self.down_factor
    }

    /// Returns the risk-free factor of the [`Model`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Model, ModelError};
    /// let model: Model = Model::new(100_f64, 2, 0.5, 1.0, 2.0).unwrap();
    /// assert_eq!(model.risk_free_factor(), 1.0);
    /// ```
    #[inline]
    pub fn risk_free_factor(&self) -> f64 {
        self.risk_free_factor
    }

    /// Returns the [`Up`] factor of the [`Model`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Model, ModelError};
    /// let model: Model = Model::new(100_f64, 2, 0.5, 1.0, 2.0).unwrap();
    /// assert_eq!(model.up_factor(), 2.0);
    /// ```
    #[inline]
    pub fn up_factor(&self) -> f64 {
        self.up_factor
    }

    /// Returns the riskneutral probability for [`Up`] in the [`Model`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Model, ModelError};
    /// let model: Model = Model::new(100_f64, 2, 0.5, 1.0, 2.0).unwrap();
    /// assert!(model.up_prob() - 1.0/3.0 <= f64::EPSILON);
    /// ```
    #[inline]
    pub fn up_prob(&self) -> f64 {
        self.up_prob
    }

    /// Returns the riskneutral probability for [`Down`] in the [`Model`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Model, ModelError};
    /// let model: Model = Model::new(100_f64, 2, 0.5, 1.0, 2.0).unwrap();
    /// assert!(model.down_prob() - 2.0/3.0 <= f64::EPSILON);
    /// ```
    #[inline]
    pub fn down_prob(&self) -> f64 {
        self.down_prob
    }

    /// Returns the stock price based on a specific [`Branch`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Branch, Model, ModelError};
    /// let model: Model = Model::new(100_f64, 2, 0.5, 1.0, 2.0).unwrap();
    /// let branch: Branch = Branch::new(3_u128, 2).unwrap(); // (Up, Up)
    /// assert_eq!(model.stock_price(&branch), 400_f64);
    /// let branch: Branch = Branch::new(0_u128, 2).unwrap(); // (Down, Down)
    /// assert_eq!(model.stock_price(&branch), 25_f64);
    /// ```
    #[inline]
    pub fn stock_price(&self, branch: &Branch) -> f64 {
        let ups: i32 = branch.ups() as i32;
        let downs: i32 = branch.downs() as i32;

        self.initial_stock_price * self.up_factor.powi(ups) * self.down_factor.powi(downs)
    }

    /// Returns the stock price history based on a specific [`Branch`].
    ///
    /// This starts from the initial stock price.
    ///
    /// This can be used for [`ContingentClaim`] that depend on the complete [`Branch`] and not only the end value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Branch, Model, ModelError};
    /// let model: Model = Model::new(100_f64, 2, 0.5, 1.0, 2.0).unwrap();
    /// let branch: Branch = Branch::new(3_u128, 2).unwrap(); // (Up, Up)
    /// assert_eq!(model.price_history(&branch), vec![100.0, 200.0, 400.0]);
    /// let branch: Branch = Branch::new(0_u128, 2).unwrap(); // (Down, Down)
    /// assert_eq!(model.price_history(&branch), vec![100.0, 50.0, 25.0]);
    /// ```
    #[inline]
    pub fn price_history(&self, branch: &Branch) -> Vec<f64> {
        let mut price: f64 = self.initial_stock_price;
        let up_factor: f64 = self.up_factor;
        let down_factor: f64 = self.down_factor;

        let mut prices: Vec<f64> = Vec::with_capacity(branch.len() + 1);
        prices.push(price);

        for tick in branch.iter() {
            match tick {
                Up => price *= up_factor,
                Down => price *= down_factor,
            }
            prices.push(price)
        }

        prices
    }

    /// Returns the risk-free probability of a specific [`Branch`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{Branch, Model, ModelError};
    /// let model: Model = Model::new(100_f64, 2, 0.5, 1.0, 2.0).unwrap();
    /// let branch: Branch = Branch::new(3_u128, 2).unwrap(); // (Up, Up)
    /// assert!(model.probability(&branch) - 1.0/3.0 * 1.0*3.0 <= f64::EPSILON);
    /// let branch: Branch = Branch::new(0_u128, 2).unwrap(); // (Down, Down)
    /// assert!(model.probability(&branch) - 2.0/3.0 * 2.0*3.0 <= f64::EPSILON);
    /// ```
    #[inline]
    pub fn probability(&self, branch: &Branch) -> f64 {
        let ups: i32 = branch.ups() as i32;
        let downs: i32 = branch.downs() as i32;

        self.up_prob.powi(ups) * self.down_prob.powi(downs)
    }

    /// Calculates the risk-free initial price of a [`ContingentClaim`].
    ///
    /// This sums up the [`ContingentClaim::payout`]s weighted with the risk-free [`Model::probability`] and
    /// discounts it with a power of the risk-free interest rate.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{basic_claims::EuropeanCall, Model};
    /// let model: Model = Model::new(100_f64, 2, 0.5, 1.0, 2.0).unwrap();
    /// let claim: EuropeanCall = EuropeanCall::new(100_f64);
    /// assert!(model.initial_claim_price(&claim) - 100.0/3.0 <= f64::EPSILON);
    /// ```
    pub fn initial_claim_price<C: ContingentClaim>(&self, claim: &C) -> f64 {
        let generator: BranchGenerator = BranchGenerator::new(self.periods).unwrap(); // Safe

        // Sum over all probability weighted payouts
        let expected_payoff: f64 = generator
            .map(|branch| claim.payout(&branch, self) * self.probability(&branch))
            .sum();

        // Discount
        expected_payoff / self.risk_free_factor.powi(self.periods as i32)
    }
}

/// An enum for handling errors during the creation of [`Model`]es.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ModelError {
    /// The model allows arbitrage.
    ///
    /// A model does not allow arbitrage, when
    /// ```text
    /// down_factor < risk_free_factor < up_factor
    /// ```
    AllowsArbitrage {
        down_factor: f64,
        risk_free_factor: f64,
        up_factor: f64,
    },
}

impl ModelError {
    /// Checks if the model does allow arbitrage.
    #[inline]
    pub(crate) fn check_arbitrage(
        down_factor: f64,
        risk_free_factor: f64,
        up_factor: f64,
    ) -> Result<(), ModelError> {
        if down_factor < risk_free_factor && risk_free_factor < up_factor {
            Ok(())
        } else {
            Err(ModelError::AllowsArbitrage {
                down_factor,
                risk_free_factor,
                up_factor,
            })
        }
    }
}

impl fmt::Display for ModelError {
    fn fmt(&self, format: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ModelError::AllowsArbitrage {
                down_factor,
                risk_free_factor,
                up_factor,
            } => write!(
                format,
                "Not arbitrage free. The inequality d ({}) < 1+r ({}) < u ({}) is not correct.",
                down_factor, risk_free_factor, up_factor
            ),
        }
    }
}

impl std::error::Error for ModelError {}
