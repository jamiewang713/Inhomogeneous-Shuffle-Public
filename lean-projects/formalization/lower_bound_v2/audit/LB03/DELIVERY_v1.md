# LB-03 completed delivery v1

Status: **COMPLETE under the unchanged frozen LB-00 v1 interface.** All ten required targets, the additional conditional-mean identification, the combined lane build, and the statement/axiom check pass. No LB-03 proof obligation remains pending. Scope ends at the finite ingredients required by LB-08; occupancy approximation and lower-bound endpoints are downstream work.

Import `RiffleLowerV2.Factorial.Main`. The checked source entry point is `RiffleLowerV2/Factorial/Main.lean`. The machine-readable receipt is `audit/LB03/verification_v1.json`, containing all source hashes, exact export types, log hashes, and transitive axiom closures. The pre-proof coordinator receipt is `audit/LB00/LB03_INTERFACE_ACK_v1.md`; no shared-interface amendment was needed.

## Exact exports and source correspondence

All names below are in namespace `RiffleLowerV2.Factorial`; all target types are in `RiffleLowerV2.Targets`. These precise type ascriptions were checked in `audit/LB03/Check_v1.lean`. The expanded frozen type bodies are printed in `declaration_audit_v1.log`.

| Export | Exact type | Source / assignment correspondence |
|---|---|---|
| `exactJointFactorial` | `Targets.ExactJointFactorial` | `lem:fixed-column-factorial`: exact disjoint labelled-row formula |
| `relativeJointFactorial` | `Targets.RelativeJointFactorial` | `lem:fixed-column-factorial`: uniform arbitrary mixed relative error |
| `residualJointFactorial` | `Targets.ResidualJointFactorial` | Prescribed-row residual version of the same exact formula |
| `residualRelativeFactorial` | `Targets.ResidualRelativeFactorial` | Uniform residual factorial errors used after `eq:collision-uniform-factorials` |
| `residualMeanComparison` | `Targets.ResidualMeanComparison` | Residual mean comparison before `eq:collision-conditional-stability` |
| `bonferroniSandwich` | `Targets.BonferroniSandwich` | `eq:collision-bonferroni-sandwich` in `lem:central-window` |
| `bonferroniProduct` | `Targets.BonferroniProduct` | Full product remainder in `lem:central-window` |
| `centralComparison` | `Targets.CentralComparison` | Two-variable finite comparison in `lem:central-window` |
| `centralComparisonOne` | `Targets.CentralComparisonOne` | One-variable finite comparison in `lem:central-window` |
| `rareSandwich` | `Targets.RareSandwich` | Assigned rare-category sandwich, with coefficient 1/3 |

Additional checked export: `conditional_wordCount_eq_residualWordMean`. Its exact type is printed in the same audit log. It identifies `Targets.residualWordMean cuts p w` with the canonical conditional expectation of `wordCount w` after subtracting all prescribed occurrences of w, under b<N, injective prescribed labels, and positive prescription probability.

## Proved dependency ledger

| Obligation | Checked implementation and dependency | Status |
|---|---|---|
| Full-word occupancy cardinality and arbitrary factorial expansion | `Requests`: fiber-embedding equivalences and distinct full words imply globally disjoint labelled requests | Proved |
| One-column request probability | `Exact`: canonical assignment relabeling, constant request probabilities, and colored-embedding double counting | Proved |
| Actual matrix mixed moments | `Exact`: actual uniform product-column law and request expansion; no abstract moment premise | Proved |
| Residual admissibility, deletion, and conditional transport | `Residual`: explicit restriction/gluing equivalence of the prescription-event subtype with canonical residual samples | Proved |
| Exact residual moments and actual residual mean | `Residual`: the transport theorem discharges the concrete law, then specializes checked exact moments | Proved |
| Positive falling-factorial ratios and logarithmic errors | `Ratios` and `Relative`: finite smallness conditions, requested-pile positivity, zero-request separation, and sum of squared multiplicities | Proved |
| Uniform original/residual relative estimates | `MomentScales`, `RelativeFromExact`, `RelativeTargets`: uniform thresholds and concrete exact exports; internal exact-moment inputs are fully discharged | Proved |
| Uniform residual mean comparison | `ResidualEstimates`: finite product-log comparison with explicit removal budget | Proved |
| Pointwise polynomial and product remainders | `Bonferroni`: finite binomial identity valid for every count, including counts above m | Proved |
| Scalar exponential benchmark | `PoissonPolynomial`: absolutely summable exponential weights and binomial moments, with the full all-count sandwich | Proved |
| Finite probability comparisons | `PolynomialMoments`, `Central`: exact coefficient expansion and (m,m) remainder using total order 2m | Proved |
| Corrected rare-category inequality | `Basic`: pointwise natural-count inequality, then canonical finite expectation | Proved |

R=0, K=0, empty word families, and zero unrequested piles are included by the checked general statements. The exact identity includes the frozen N=0 case. Residual prescriptions may contain repeated full words and the tested word; the deleted-row statistic is proved on the conditioning event. The b=0 mean comparison has exactly zero error. Even m=2 and counts n=0,1 are covered by the Bonferroni proof.

## Constants and uniform thresholds

The original relative theorem uses `D = 4 / min(c,1)`. The residual relative theorem uses `D = 4 / min(c/2,1/2)`. The residual mean theorem uses `D = 4*(1+1/c)`.

`eventual_factorial_budgets` proves a threshold B(a,C) such that, for every N at or above it, N>=2,

- `2*N^(1/5) <= a*N`, and
- `(2/a)*(C*log N+1)*(N^(1/5))^2/N <= 1`.

The original theorem chooses a=min(c,1) and this threshold. The residual theorem chooses a=min(c/2,1/2) and enlarges it to `max(B(a,C), max(2*b0+2, ceil(2*b0/c)))`. Thus residual piles and population are at least aN. The finite numerical theorem keeps ambient N separate from population M=N-b, so the frozen order bound remains R<=N^(1/5).

The mean threshold similarly comes from the proved convergence of `2*(1+1/c)*(C*log N+1)*b0/N` to zero, enlarged by the same removal thresholds. Every threshold is chosen after c,C (and b0 residually), before N,k,K,d, counts, words, orders, and prescriptions. The bounds are uniform over all those variables. These are proved finite quantified thresholds, with no sequence of arrays fixed in advance.

The central comparisons preserve exactly the frozen constants: epsilon times `(1+mu)*(1+nu)*exp(mu+nu)` plus three times the stated sum/product of Poisson remainders, and the corresponding one-variable bound. The rare lower coefficient on the third falling factorial is exactly 1/3.

## Verification and provenance

Successful combined build, run from `formalization/lower_bound_v2`:

```text
python3 scripts/lane.py LB03 RiffleLowerV2.Factorial.Main
```

Log: `audit/LB03/lane_build_v1.log`, ending in `LB03 BUILD_OK`. The lane command recompiled all owned imported sources in `.build/lanes/LB03/lib/lean`, and verified the frozen source/contract identities and pinned runtime/dependencies. Two tactic-style linter warnings are recorded; there are no proof errors.

The statement and axiom probe `audit/LB03/Check_v1.lean` ran with the same Lean 4.33.1 compiler and private lane import path, exiting 0. Log: `audit/LB03/declaration_audit_v1.log`. All eleven exported theorem closures use exactly `propext`, `Classical.choice`, and `Quot.sound`. All fifteen owned proof modules pass the prohibited-proof-token scan. There are no custom axioms, proof placeholders, native proof oracles, or unproved concrete-moment premises.

Lean: 4.33.1. Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`. Frozen v1 manifest hash remains `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`; manuscript hash remains `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`.

`basic_provenance_v1.json` records elementary finite-PMF source references. `exact_residual_provenance_v2.json` records the checked local source port of the residual restriction/gluing proof, preserving its earlier pending snapshot. There are no imports of LB01/LB02 proof modules and no historical cache imports. Shared files, historical packages, manuscript, old freezes, and other lanes were preserved.

## Independent reviews and resolutions

The three pre-proof reports (`math_review_v1.md`, `representation_review_v1.md`, `hypotheses_review_v1.md`) were compared before proofs in `REVIEW_RESOLUTION_v1.md`, after the unchanged-interface acknowledgement. They agreed the frozen statements are valid. The substantive residual-cutoff finding was resolved by the separate ambient-N finite ratio theorem. The polynomial-tail finding was resolved by the all-count pointwise remainder and its mixed (m,m) expectation.

Independent implementation reports include `finite_comparison_implementation_review_v1.md`, `central_implementation_review_v1.md` with its v2 compilation supplement, `concrete_implementation_review_v1.md` with v2/v3 supplements, and `exact_numerical_review_v1.md` / `exact_central_review_v1.md`. They approve the final mathematics, canonical-law bridges, constants, and quantifier order. The v3 concrete supplement checks that no exact-moment premise remains in either public relative theorem. No substantive review finding remains unresolved. Original reports and development logs are retained as history; this delivery and `verification_v1.json` state the final checked status.

Downstream receipt: import `RiffleLowerV2.Factorial.Main` and use the ten exact exports above. LB00 may integrate the completed lane using its serialized package-build workflow; this lane did not modify package configuration, umbrella imports, shared contracts, or dependency caches.
