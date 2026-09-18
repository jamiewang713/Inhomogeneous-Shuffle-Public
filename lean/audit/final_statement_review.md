# Final independent statement-fidelity review

This review is read-only with respect to the implementation modules. It compares the completed declarations against `FROZEN_CONTRACT.md` and the earlier independent representation review.

| Contract | Modules inspected | Finding |
| --- | --- | --- |
| F1 | `FiniteLawExtras.lean`, with the previously reviewed `FiniteLaw.lean` | `prob_exists_le_sum` is the full finite-family union bound, including an empty index type. No nonempty-event or positive-mass premise was inserted. The PMF event bridge identifies the finite probability with `ENNReal.ofReal` of the real finite sum. Its measurable-space typeclasses are infrastructure for the mathlib representation, not additional hypotheses on a hypergeometric experiment. |
| H0 | `SubsetSampling.lean`, `Hypergeometric.lean`, and the PMF bridge | The marked set is fixed and contained in the finite population; the sample-size feasibility premise is exactly D5. `sample_intersection_pointMass` proves agreement at every natural point, including points above the sample size. The fibre bijection and count use the marked and unmarked subsets; no within-column independence assumption appears. Empty populations remain legal. |
| H4 | `HypergeometricBoundary.lean` | All four deterministic parameter cases have exact expectation and point-mass formulas. `deterministic_of_variance_eq_zero` uses the proved zero-variance characterization and introduces no extra hypothesis. The positive centered-tail threshold is the frozen condition; variance zero gives probability zero. |
| N1 | `NonExhaustion.lean` | The population premise is exactly N≥2 and the nonnegative lower-bound parameters and three lower-bound inequalities are retained. The formula-level and actual-variance versions agree through the proved variance identity. These statements are standalone arithmetic implications, not ambient reserve assertions. |
| N2 | `NonExhaustion.lean` | Both reserve and residual-fraction estimates have exactly the frozen premises. The explicit nonnegative m and error premises are retained even where the algebraic proof does not need them. Neither statement assumes or claims a reserve in the shuffle construction. |
| X1 | `AmbientCounterexample.lean` | The canonical residual experiment N=2L, K=L, m=2L has the claimed exact mean, zero variance, and unit point mass. For L≥1 the sampling complement is exactly zero while both categories and the mean are positive. The endpoint theorem proves the deterministic counts below and at the middle digit for an arbitrary fixed column with the stated left and middle counts. |

## Precise scope of X1

The Lean declarations prove the exhausted residual law and deterministic first-column endpoint counts. They do **not** claim to formalize a complete embedding into all manuscript definitions of admissibility, profile truncation, fluctuation regularity, or a nonterminal retained stable pair. That embedding is the mathematical source-level counterexample described in the independent reports and the frozen contract. The code should therefore be described as a verified residual-law counterexample and verified endpoint-count obstruction; it is not a Lean theorem about the entire manuscript's ambient construction. This distinction is represented correctly in the inspected declarations, with no false ambient theorem added.

## H1–H7 and C4 public-declaration audit

The following public results were inspected using Lean's declaration dependency audit: normalization, expectation, general factorial moments, variance, zero-variance equivalence, all four deterministic expectation identities, zero centered tails, the universal concentration constant, the universal point-mass constant, and the transform comparison. Every inspected result reports only:

`[propext, Classical.choice, Quot.sound]`.

The new `ConditionalHypergeometric.lean` module specializes C4 using equality of **all** natural conditional count probabilities. Its conditioning events are explicitly positive, and it does not assume a pointwise bound on Y or an extra integrability condition. Its mean, factorial moments, variance, centered second moment, zero-variance branch, point-mass bound, and transform follow from that exact law equality. Its concentration and point-mass constants are existentially quantified before the ambient law, event, count, and feasible hypergeometric parameters. The zero-variance point-mass case is not passed to an inverse-standard-deviation bound.

The conditional expectation, variance, transform, universal concentration, and universal point-mass declarations also report only the same three standard trusted dependencies. `ConditionalHypergeometric.lean` compiles without warnings.

No discrepancy requiring a change to the frozen assumptions or mathematical conclusions was found. The X1 scope distinction above must be preserved in the final completion report.
