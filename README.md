# Cox-Ross-Rubinstein

This project uses the [Cox-Ross-Rubinstein-Model](https://en.wikipedia.org/wiki/Binomial_options_pricing_model) to price [contingent claims](https://en.wikipedia.org/wiki/Contingent_claim).

The `Model` can be set up with necessary parameters like

* Initial stock price
* Number of periods
* Down factor
* Risk-free rate
* Up factor

to represent the current market situation.
Using the `ContingenClaim` trait you can define your own claim.
A claim needs a `payoff` for every possible `Branch` the model can take.

Some basic options like

* European Put and Call
* European lookback Put and Call

are already implemented in the `basic_claims` module.

To get the "fair" pricing you can use the `initial_claim_price` method.
This uses the riskneutral expectation of the discounted end value.

## TODOs

- [ ] Add integration tests.
- [x] Add more claims to `basic_claims`.
- [ ] Implement `Simulation` to simulate risk-free branches of the stock prices.
- [ ] Use this simulation to evaluate the claim using [Monte Carlo method](https://en.wikipedia.org/wiki/Monte_Carlo_method).
- [ ] Calculate fair claim prices for any knot in the tree.
- [ ] Calculate replication strategies.
- [ ] Visualization.
