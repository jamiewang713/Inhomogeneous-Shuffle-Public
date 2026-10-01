# LB-02 independent analytic/recursion/prefix review v1

Reviewed 2026-10-01. Scope: `Thinning/Tails.lean`, `Recursion.lean`, and `PrefixCoordinates.lean`; no source edits.

**Verdict:** the inspected checked declarations match the intended analytic tails, backward affine recursion, and exact prefix-coordinate representation. No mathematical or representation correction is required. They remain generic ingredients until the concrete stochastic specializations listed below are proved.

## Checked state

`audit/LB02/analytic_build_v3.log` ends in `LB02 BUILD_OK`. All three current lane `.olean` files are newer than the corresponding inspected source. Earlier failing development logs do not supersede that successful build. A separate read-only Lean invocation imported the three compiled modules and printed axiom closures for all thirteen public theorems listed below; it exited 0. The union is exactly `propext`, `Classical.choice`, and `Quot.sound`. `vector_take_eq_iff` itself uses only `propext` and `Quot.sound`.

The inspected source identities are:

| Module | SHA-256 |
| --- | --- |
| `Tails` | `a04c6af51f20c3e3d9a255fdd18a5a2931c8dc0132a61cff61b733e3ccebfb16` |
| `Recursion` | `22c62d8a60143ecd5539bd15e068694a174da86bbda1d8e3b9d81005251832bb` |
| `PrefixCoordinates` | `9cc9f8dd40e1632feaf51753071bd7aa81c80541145ba74a1ed47721e7f8ab2a` |

The build contains minor tactic/linter diagnostics, but no failed declaration. This review certifies the listed source snapshot and actual imported declarations, not later edits or entire-lane completion.

## Mathematical correspondence

`Tails.lean` exports `chernoffConstant_pos`, `centered_exp_of_transform`, `bernstein_of_transform`, `half_mean_of_transform`, and `less_two_of_transform`. They use a genuine normalized finite PMF and a natural-valued count. Their generic input is the all-positive-parameter bound `E[s^X] ≤ exp(μ(s-1))`; no independence is asserted. The centered-exponential step applies the checked remainder bound for `|z|≤1` and multiplies by nonnegative μ. The Bernstein choice `z=t/[2(μ+t)]` has positive denominator for every `μ≥0,t>0`, including μ=0. Markov and the two-tail union give exactly `2 exp(-t²/[4(μ+t)])`.

The lower-half theorem uses `s=1/2`, a positive exponential threshold, and the exact constant `(1-log 2)/2`; `chernoffConstant_pos` proves its strict positivity. The `X<2` theorem uses integrality to restrict X to 0 or 1 and obtains exactly `2 exp(-μ/2)`. The last two generic results require no separate μ≥0 hypothesis, which is legitimate: their calculations need none. Concrete callers still must identify the required nonnegative mean.

`Recursion.lean` exports `affine_pos`, `independent_intersection_transform`, and `binomial_le_exp`. Its domain is a uniform law on a dependent finite product of nonempty coordinate spaces. The one-coordinate hypothesis is quantified over **every deterministic marked set A**, with exponent `A.card`. This is the necessary strength for iteration. The induction uses the exact finite product expectation identity, applies the suffix theorem conditional on the fixed first coordinate, and then integrates that coordinate at positive affine base `z=1-Q+Qs`. It therefore implements backward affine recursion without assuming independent rows.

The empty sequence gives the deterministic count `A.card`. Products stay in `[0,1]`, and `affine_pos` explicitly accommodates q=0 and q=1. The population remains the common ambient `Fin M`; current surviving-cardinality is the changing marked-size parameter. The final analytic step raises `1+v≤exp(v)` using a positive affine base and yields precisely `exp(M Q(s-1))`.

`PrefixCoordinates.lean` exports `vector_take_eq_iff`, `prefix_coordinates_iff`, `prod_prefix_extension`, `prefixColumnFraction_product`, and `prefixColumnFraction_bounds`. List equality is equivalent to equality at exactly the prefix's existing coordinates. The neutral suffix factors equal one, so the full-column product is exactly the shared dimensionless `RiffleLowerV2.prefixMass`, with no unused-suffix multiplicity. Active fractions are `cuts.count/N` and their `[0,1]` bounds use the exact column sum and N>0. Empty prefixes, empty column sequences, and zero-count digits remain in the statements.

## Specializations still required outside these three modules

1. Prove the exact one-step transform for the **actual** uniformly permuted size-m subset and every deterministic marked set; connect its count to the hypergeometric law and discharge `M>0,m≤M`. The frozen initial-segment target alone needs a relabeling/general-marked-set bridge.
2. Instantiate the recursion with those subset coordinate laws, prove its `intersectionWithin` count equals frozen `thinningCount`, and export the exact `SuccessiveThinning` theorem plus abstract tails.
3. For canonical `ColumnAssignments`, prove that a specified digit's row set has the actual uniform fixed-size subset law (or directly prove the equivalent all-s transform). Discharge the active-column one-step bound and the deterministic neutral-suffix bound. Then prove `intersectionWithin univ prefixColumnSet` has cardinality `prefixCount`, use `prefixColumnFraction_product`, and obtain the actual prefix transform and `PrefixTails`. The coordinate iff alone is not this probability-law bridge.
4. Feed that proved `PrefixTails` theorem to the separately checked `allPrefixConcentration_of_prefixTails`; the simultaneous bound must not retain an unproved target premise at the public frozen export.
5. Specialize the residual law to residual prefix/count transforms and all three tails with population `N-b`, subtracted digit counts, and positive conditioning probability. None of the three modules inspected here establishes that conditioning law.
6. Combine actual prefix tails with deterministic canonical-maximal-word selection and mean identity to export the requested maximal-word exponential count tail. The physical permutation/run/TV bridge remains outside LB-02.

These are integration obligations, not discovered counterexamples or reasons to weaken a frozen target. No ancestor-family premise, positive-pile restriction, row independence, or temporal regularity is needed by the inspected proofs.
