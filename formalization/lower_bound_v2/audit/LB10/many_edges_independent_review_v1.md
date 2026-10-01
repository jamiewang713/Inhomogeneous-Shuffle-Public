# LB10 independent collision-mean and many-edge review v1

The reviewer authored neither reviewed proof module. The review read both complete sources line by line, the exact frozen `ManyEdgesTarget` and shared `GeometrySpec`/`ColdLocalization` definitions, the relevant actual occupancy marginal/variance and lower-tail helpers, and the manuscript proof of `lem:many-edges`. No source was modified.

## Source identity and build evidence

| Source/artifact | SHA-256 |
|---|---|
| `RiffleLowerV2/EmpiricalLower/CollisionMean.lean` | `9ee70a58b6eea506c4709fb3b6b40c5f55492c3bf232f09b1312ef917234c85e` |
| `RiffleLowerV2/EmpiricalLower/ManyEdges.lean` | `a160b8a63bb5417bdf8db8c6ec5f49aa6e636b2b25299ec2b2baa4ec79557483` |
| `audit/LB10/many-edges-dev06.log` | `f8f047cd8cec4ef4cf5b43524e40205670c1aab3ca6db31a1390bca669ad03ed` |

The inspected final component log reports `LB10 BUILD_OK` without warnings or errors. No concurrent build or cache mutation was initiated for this review; the coordinator is separately running the complete Main build and full axiom/export audit.

**Verdict:** the sources establish the frozen many-edge target by the intended actual-model argument. No mathematical, hypothesis, representation, constant, or quantifier finding remains open.

## Marginal and expectation lower bound

`coldMeanConstant_pos` and `coldMeanConstant_eq` correctly establish the absolute positive value `exp(-5)/4`:

`(exp(-1)/4)*(exp(-2))² = exp(-5)/4`.

`cold_min_mean` handles all mean regimes without adding an upper bound on u. For N≥1 and kappa0≥0, the loss factor `N^(-4*kappa0)` is at most one. Therefore the lower mass bound `exp(-2)N^z≤u` gives

`exp(-4)N^(2z-4*kappa0) ≤ u²`.

The independent inequality `z≤2*kappa0` makes the same expression at most one. Taking the minimum gives exactly the needed saturation estimate, including tiny means, means greater than one, and negative z. All square/rpow comparisons use nonnegative factors and a strictly positive population.

`geometry_selectedPiles` extracts the exact shared lower digit fractions and multiplies by the proved positive N. Its conclusion is literally `selectedPiles` with the fixed constant `min xi (min chi (1/k))` and actual full-word family.

`cold_collision_mean_lower` uses the lower half of the supplied absolute marginal error. With `D*N^(-1/100)≤1/2` and nonnegative Poisson collision probability, the true collision probability is at least half the Poisson value. The checked LB08 lower bound contributes `exp(-1)/2 * min(u²,1)`, hence the resulting coefficient is `exp(-1)/4` before the squared geometric mass loss. Combining with `cold_min_mean` produces `coldMeanConstant*N^(2z-4*kappa0)` for each selected word.

The expectation is the finite sum of these actual collision probabilities by `Occupancy.expect_eventCount`; no occupancy independence is asserted. The exact family cardinality `N^(hp+ht)` and definition `g=2z+hp+ht` then give `E Z≥coldMeanConstant*N^(g-4*kappa0)`. The mass and cardinality fields are read from the same cuts,W,G and hN throughout. Generic marginal and small-error premises occur only in this intermediate helper and are supplied by actual occupancy results in `manyEdges`.

## Exponent slack and finite constants

`cold_exponent_slack` uses only the frozen `kappa/2≤g-h/2` and `kappa0≤kappa/100`. Its exact arithmetic is

`kappa/2-4*kappa/100 = 23*kappa/50 = kappa/3+19*kappa/150`.

Since eta>0, the retained `19*kappa/150` is strictly positive. Thus the manuscript's strict margin beyond kappa/3 is explicit and uniform over varying g,h.

`exists_cold_mean_threshold` selects thresholds for `N^(19*kappa/150)≥2/coldMeanConstant` and `N^(kappa/12)≥2`, depending only on eta and the absolute constant. `cold_mean_dominates` bounds `sqrt M≤2N^(h/2)` from `M≤2N^h`; this harmless factor two is absorbed by the first threshold. The remaining powers give precisely `sqrt M*N^(kappa/3)≤E Z`.

`cold_mean_power_lower` uses `M≥N^(kappa/3)` to prove `E Z≥N^(kappa/2)>0`. `cold_half_mean_threshold` uses the second threshold and `kappa/4+kappa/12=kappa/3` to obtain `sqrt M*N^(kappa/4)≤E Z/2`. Finally `cold_edges_threshold` uses `0<M≤N`, N≥1, and kappa>0 to prove

`M^(1/2+kappa/5)≤sqrt M*N^(kappa/4)`.

Every real power has a positive base where logarithmic or additive exponent identities are used. Every reciprocal is introduced only after its denominator is proved positive. No finite coefficient is silently discarded.

## Uniform occupancy and concentration

In `manyEdges`, k,T,eta,rho,chi,xi,P,epsilon and their positivity hypotheses are fixed before selecting any threshold. The selected-pile constant c depends only on the already fixed k,xi,chi. `Occupancy.uniformOccupancy c T` supplies D and its threshold uniformly over all later cuts and selected words. The actual horizon depth satisfies `K=floor(T log N)≤T log N`, with N≥2 guaranteed by the numerical threshold.

The same returned occupancy theorem supplies both the true marginal bound and the true variance bound `Var Z≤E Z+D*N^(-1/100)*(E Z)²`. The module does not assume either result for the final target. Its `hsmall` is obtained from `N^(-1/100)≤1/(2D)`, while `hsmallE` uses the other side of the chosen minimum to get `4D*N^(-1/100)≤epsilon/4`.

The expectation lower bound proves positivity before applying `Occupancy.lower_tail_success` at t=1/2. The actual bound is `P(Z>E Z/2)≥1-4/(E Z)-4D*N^(-1/100)`. Passing from strict to weak success only enlarges the event. The independent threshold `N^(-kappa/2)≤epsilon/16`, together with `E Z≥N^(kappa/2)`, yields `4/(E Z)≤epsilon/4`. Hence collision success has probability at least `1-epsilon/2`, uniformly in all supplied witnesses and cuts.

The final N0 is the maximum of the occupancy, mean-constant, localization, marginal/variance-error, and reciprocal-mean thresholds. Each is selected before N,cuts,hN,W,G. Their use through the maximum is explicit. Neither family cardinality nor the varying exponents g,h enters threshold selection.

## Localization intersection and the exact target

`probability_intersection_lower` is the elementary indicator union-bound consequence `P(A∩B)≥P(A)+P(B)-1`; it invokes no independence. The completed LB09 `localization` theorem supplies the actual `ColdLocalization` probability at least `1-epsilon/2`, using precisely the frozen witness and geometry specs.

`collisionCount_eq_card` identifies Z with the real cast of the number of selected words with at least two copies. The second conjunct of actual `ColdLocalization` already supplies the proved injective assignment into `shuffleEdges ∩ internalEdges` at the actual ambient prefix lower-rank translate. Its natural cardinality inequality is cast to reals and composed with the half-mean and edge-threshold bounds. Thus every sample in the concentration/localization intersection satisfies the exact desired edge event.

The exported declaration is literally

```lean
RiffleLowerV2.EmpiricalLower.manyEdges :
  RiffleLowerV2.Targets.ManyEdgesTarget
```

Its event retains the exponent `1/2+kappa eta/5`, the actual shuffle graph, the same relative set, and the exact integer lower-rank translate. The only supplied witness/geometry premises are those explicitly present in the frozen intermediate target; no marginal, variance, concentration, localization, independence, or success assumption is added. The previously reviewed `coldOnly` constructs these witnesses and specs from empirical/local-good cut assumptions, so they do not leak into the physical cold or combined endpoints. No macroscopic TimeLaw or analytic regularity premise enters either source.
