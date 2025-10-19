//! This module contains the implementations of the model struct.

use random::FastBernoulli;
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
    /// assert!((model.probability(&branch) - 1.0/3.0 * 1.0/3.0).abs() <= f64::EPSILON);
    /// let branch: Branch = Branch::new(0_u128, 2).unwrap(); // (Down, Down)
    /// assert!((model.probability(&branch) - 2.0/3.0 * 2.0/3.0).abs() <= f64::EPSILON);
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
    /// let model: Model = Model::new(100_f64, 2, 0.5, 1.0, 1.5).unwrap();
    /// let claim: EuropeanCall = EuropeanCall::new(100_f64);
    /// let claim_price: f64 = model.initial_claim_price(&claim);
    /// assert!((claim_price - 31.25).abs() <= f64::EPSILON);
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

    /// Calculates the risk-free current price of a [`ContingentClaim`] based on a [`Branch`].
    ///
    /// This **recursively** calculates the claim value based on
    /// ```text
    /// claim_value[branch] = claim_value[branch + Up] * q + claim_value[branch + Down] * (1 - q)
    /// ```
    /// where `q` is the riskneutral probability for one [`Up`]-movement.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{basic_claims::EuropeanCall, Branch, ContingentClaim, Model, Tick};
    /// // Value in [Up, Up]
    /// let model: Model = Model::new(100_f64, 3, 0.5, 1.0, 2.0).unwrap();
    /// let claim: EuropeanCall = EuropeanCall::new(100_f64);
    /// let branch: Branch = Branch::from_ticks(vec![Tick::Up, Tick::Up].as_ref()).unwrap();
    /// let claim_value: f64 = model.claim_value(&claim, &branch).unwrap();
    /// assert!((claim_value - 300.0).abs() <= f64::EPSILON);
    /// // Initial value
    /// let branch: Branch = Branch::from_ticks(vec![].as_ref()).unwrap();
    /// let claim_value: f64 = model.claim_value(&claim, &branch).unwrap();
    /// let initial_price: f64 = model.initial_claim_price(&claim);
    /// assert!(claim_value - initial_price <= f64::EPSILON);
    /// // End value
    /// let ticks: Vec<Tick> = vec![Tick::Up, Tick::Up, Tick::Down];
    /// let branch: Branch = Branch::from_ticks(&ticks).unwrap();
    /// let claim_value: f64 = model.claim_value(&claim, &branch).unwrap();
    /// let claim_payout: f64 = claim.payout(&branch, &model);
    /// assert!((claim_value - claim_payout).abs() <= f64::EPSILON);
    /// ```
    pub fn claim_value<C: ContingentClaim>(
        &self,
        claim: &C,
        branch: &Branch,
    ) -> Result<f64, ModelError> {
        let branch_length: usize = branch.len();
        let model_length: usize = self.len();

        ModelError::check_branch(branch_length, model_length)?;

        if branch_length == model_length {
            Ok(claim.payout(branch, self))
        } else if branch_length == 0 {
            Ok(self.initial_claim_price(claim))
        } else {
            let up_branch: Branch = branch.add_unchecked(Up); // Safe
            let down_branch: Branch = branch.add_unchecked(Down); // Safe

            let up_value: f64 = self.claim_value(claim, &up_branch)?;
            let down_value: f64 = self.claim_value(claim, &down_branch)?;

            Ok((up_value * self.up_prob + down_value * self.down_prob) / self.risk_free_factor)
        }
    }

    /// Replicates a [`ContingentClaim`] based on a [`Branch`].
    ///
    /// This uses the **recursive** method [`Model::claim_value`] to calculate the possible values one time period in the future.
    /// The number of stocks and bonds is calculated by solving
    /// ```text
    /// claim_value[branch + Up] = #bonds * risk_free_factor**t + #stocks * stock_price[branch + Up]
    /// claim_value[branch + Down] = #bonds * risk_free_factor**t + #stocks * stock_price[branch + Down]
    /// ```
    /// where `t` is the length of the [`Branch`] plus one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{basic_claims::EuropeanCall, Branch, ContingentClaim, Model, Tick};
    /// let model: Model = Model::new(100_f64, 3, 0.5, 1.0, 2.0).unwrap();
    /// let claim: EuropeanCall = EuropeanCall::new(100_f64);
    /// let branch: Branch = Branch::from_ticks(vec![Tick::Up, Tick::Up].as_ref()).unwrap();
    /// let (number_of_bonds, number_of_stocks): (f64, f64) = model.replicate_claim(&claim, &branch).unwrap();
    /// assert!((number_of_bonds + 100.0).abs() <= f64::EPSILON);
    /// assert!((number_of_stocks - 1.0).abs() <= f64::EPSILON);
    /// ```
    pub fn replicate_claim<C: ContingentClaim>(
        &self,
        claim: &C,
        branch: &Branch,
    ) -> Result<(f64, f64), ModelError> {
        ModelError::check_branch(branch.len() + 1, self.len())?;

        let up_branch: Branch = branch.add_unchecked(Up); // Safe
        let down_branch: Branch = branch.add_unchecked(Down); // Safe

        let bond_price: f64 = self.risk_free_factor.powi(branch.len() as i32 + 1_i32);

        let up_price: f64 = self.stock_price(&up_branch);
        let down_price: f64 = self.stock_price(&down_branch);
        let up_value: f64 = self.claim_value(claim, &up_branch)?;
        let down_value: f64 = self.claim_value(claim, &down_branch)?;

        let number_of_stocks: f64 = (up_value - down_value) / (up_price - down_price);
        let number_of_bonds: f64 = (up_value - number_of_stocks * up_price) / bond_price;
        Ok((number_of_bonds, number_of_stocks))
    }

    /// Calculates the value of a portfolio consisting of a `number_of_bonds` and a `number_of_stocks`
    /// on a specific [`Branch`].
    ///
    /// This is calculated using
    /// ```text
    /// risk_free_factor**t * #bonds + stock_price[branch] * #stocks
    /// ```
    /// where `t` is the length of the [`Branch`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{basic_claims::EuropeanCall, Branch, ContingentClaim, Model, Tick};
    /// let model: Model = Model::new(100_f64, 3, 0.5, 1.0, 2.0).unwrap();
    /// let claim: EuropeanCall = EuropeanCall::new(100_f64);
    /// let branch: Branch = Branch::from_ticks(vec![Tick::Up, Tick::Up].as_ref()).unwrap();
    /// let (number_of_bonds, number_of_stocks): (f64, f64) = model.replicate_claim(&claim, &branch).unwrap();
    ///
    /// let claim_value: f64 = model.claim_value(&claim, &branch).unwrap();
    /// let cost_of_replication: f64 = model.portfolio_value(number_of_bonds, number_of_stocks, &branch);
    /// assert!((claim_value - cost_of_replication).abs() <= f64::EPSILON);
    /// ```
    pub fn portfolio_value(
        &self,
        number_of_bonds: f64,
        number_of_stocks: f64,
        branch: &Branch,
    ) -> f64 {
        let bond_value: f64 = self.risk_free_factor.powi(branch.len() as i32) * number_of_bonds;
        let stock_value: f64 = self.stock_price(&branch) * number_of_stocks;

        bond_value + stock_value
    }

    /// Simulates a [`Branch`] based  on the `Up`-probability of  the [`Model`].
    ///
    /// This uses [`FastBernoulli`] to generate the [`Branch`] at lightning speed.
    #[inline]
    fn simulate_branch(&self, rng: &mut FastBernoulli) -> Branch {
        let mut ticks: u128 = 0_u128;

        for index in 0..self.len() {
            let is_up: bool = rng.bernoulli(self.up_prob);
            if is_up {
                ticks |= 1 << index
            }
        }

        Branch::new_unchecked(ticks, self.len())
    }

    /// Calculates the initial price of a [`ContingentClaim`] using Monte Carlo Simulation.
    ///
    /// More simulations yields a more accurate result.
    ///
    /// # Arguments
    ///
    /// * `claim`: The [`ContingentClaim`] to calculate the price of.
    /// * `number_of_simulations`: The number of simulations.
    ///
    /// # Returns
    ///
    /// An approximation of the initial price of a [`ContingentClaim`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use cox_ross_rubinstein::{basic_claims::EuropeanCall, Branch, ContingentClaim, Model, Tick};
    /// let model: Model = Model::new(100_f64, 3, 0.5, 1.0, 2.0).unwrap();
    /// let claim: EuropeanCall = EuropeanCall::new(100_f64);
    /// let simulated_price: f64 = model.simulate_claim_price(&claim, 10_000);
    /// let initial_price: f64 = model.initial_claim_price(&claim);
    /// assert!((simulated_price - initial_price).abs() <= 5.0);
    /// ```
    pub fn simulate_claim_price<C: ContingentClaim>(
        &self,
        claim: &C,
        number_of_simulations: usize,
    ) -> f64 {
        let mut rng: FastBernoulli = FastBernoulli::new();
        let mut payoffs: f64 = 0_f64;

        for _ in 0..number_of_simulations {
            let branch: Branch = self.simulate_branch(&mut rng);
            payoffs += claim.payout(&branch, self);
        }

        let discount_rate: f64 = self.risk_free_factor.powi(self.periods as i32);

        payoffs / (number_of_simulations as f64) / discount_rate
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

    /// The [`Branch`] is too long for the [`Model`].
    BranchTooLong {
        branch_length: usize,
        model_length: usize,
    },
}

impl ModelError {
    /// Checks if the [`Model`] does allow arbitrage.
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

    /// Checks if a [`Branch`] and a [`Model`] are compatible.
    #[inline]
    pub(crate) fn check_branch(
        branch_length: usize,
        model_length: usize,
    ) -> Result<(), ModelError> {
        if branch_length <= model_length {
            Ok(())
        } else {
            Err(ModelError::BranchTooLong {
                branch_length,
                model_length,
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
            ModelError::BranchTooLong {
                branch_length,
                model_length,
            } => {
                write!(
                    format,
                    "Branch of length {} is too long for model fo length {}.",
                    branch_length, model_length
                )
            }
        }
    }
}

impl std::error::Error for ModelError {}
