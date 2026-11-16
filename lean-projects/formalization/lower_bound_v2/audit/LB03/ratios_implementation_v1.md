# LB03 numerical factorial implementation receipt v1

Date: 2026-10-01. The numerical work is complete and concretely connected to the canonical exact-moment exports.

## Checked frozen exports

```lean
RiffleLowerV2.Factorial.relativeJointFactorial :
  RiffleLowerV2.Targets.RelativeJointFactorial

RiffleLowerV2.Factorial.residualRelativeFactorial :
  RiffleLowerV2.Targets.ResidualRelativeFactorial

RiffleLowerV2.Factorial.residualMeanComparison :
  RiffleLowerV2.Targets.ResidualMeanComparison
```

The first two exports are in `Factorial/RelativeTargets.lean`; the third is in `Factorial/ResidualEstimates.lean`. Import `RiffleLowerV2.Factorial.RelativeTargets` to obtain all three and their concrete exact-moment dependencies. The lane's `Main` imports this module.

## Proof/dependency ledger

| Obligation | Checked implementation | Dependency status |
|---|---|---|
| Controlled scalar logarithm | `abs_log_one_sub_le`: `0≤x≤1/2 → abs(log(1-x))≤2x` | Proved from trusted elementary log inequalities |
| Exponentiation of log error | `relative_error_of_log`: positive x,y and `abs(log(x/y))≤e≤1` give `abs(x-y)≤2ey` | Proved using trusted exponential remainder bound |
| Falling correction | `fallingCorrection`, positivity/recurrence, `log_fallingCorrection_bound` | Proved, with `0<n` and `2r≤n`; bound `r²/n` |
| Zero unrequested piles | `column_log_factorial_bound` | Order-zero branch is evaluated before logarithms; no positivity imposed on unrequested piles |
| Exact monomial normalization | `requestedCount_sum`, `requested_monomial`, `factorial_benchmark_identity`, `numericalMean_product_benchmark` | Proved finite rearrangements |
| Uniform finite ratio | `relativeFactorial_finite` | Proved for separate ambient N and actual population M |
| Eventual uniform scales | `momentCutoff_ratio_tendsto`, `momentBudget_tendsto`, `eventual_factorial_budgets` | Proved from trusted power/log limits |
| Actual original relative moment | `relativeJointFactorial` | `relativeJointFactorial_of_exact` applied to checked `exactJointFactorial`; no remaining premise |
| Actual residual relative moment | `residualRelativeFactorial` | `residualRelativeFactorial_of_exact` applied to checked `residualJointFactorial`; no remaining premise |
| Residual mean error | `residualMean_finite`, `residualBudget_tendsto`, `residualMeanComparison` | Proved directly from numerical counts; conditional first-moment identification is the exact worker's checked `conditional_wordCount_eq_residualWordMean` |

The `_of_exact` lemmas are explicitly named internal transport interfaces. Their inputs are discharged in the final frozen exports; no abstract conditional theorem is being substituted for a concrete matrix-law result.

## Constants, thresholds, and domains

- Original relative moments use **`D=4/min(c,1)`**.
- Residual relative moments use **`D=4/min(c/2,1/2)`**.
- Residual mean comparison uses **`D=4(1+1/c)`**.

The finite comparison assumes a common lower bound `aN` for the actual population M and every positively requested pile, together with `2R≤aN`. Its log budget is `(2/a)(K+1)R²/N`; if this is at most one, the relative-error constant is `4/a`. Thus it applies directly to residual population `M=N-b` while retaining the frozen ambient cutoff `R≤N^(1/5)`.

Threshold witnesses are obtained from proved convergence of `2N^(1/5)/N` and `(2/a)(C log N+1)(N^(1/5))²/N`, then enlarged to include `N≥2`. Residual thresholds are additionally enlarged by `max(2b0+2, ceil(2b0/c))`. The mean threshold comes from convergence of `2(1+1/c)(C log N+1)b0/N` and the same population/pile enlargements. Each threshold is chosen after exactly the fixed parameters allowed by the contract, and before all variable counts, words, orders, row prescriptions, and column depths.

The residual subtraction bounds are proved using `usedCount≤b`, natural-subtraction compatibility, `N-b≥N/2`, and selected original piles at least `cN`. No dependence on a thinning implementation or on LB01/LB02 occurs.

Boundary cases are retained by the checked statements: `R=0`, zero column depth, empty word families, zero-order requests in zero piles, and `b=0`. The residual mean right side vanishes for `b=0` and the proof establishes exact equality. Original/residual exact formulas cover their broader boundary domains through the separate combinatorial exports.

## Source correspondence and provenance

`lem:fixed-column-factorial` supplies the falling-factorial logarithmic argument and exact monomial normalization. Residual estimates implement the conditioning/deletion applications following that lemma, especially manuscript lines 3830–3834 and 3898–3907. The frozen residual targets are in `Contracts/v1/AdditionalFinite.lean` and `Contracts/v1/TransferFinite.lean`.

These numerical proofs were written for the pinned Lean 4.33.1 package and checked against its shared definitions and trusted mathlib. No historical project cache, first/second-moment shortcut, custom axiom, placeholder, or native proof oracle was introduced. All shared files, contracts, freezes, and manuscript sources remain unchanged by this worker.

## Verification

Successful concrete build, from `formalization/lower_bound_v2`:

```text
python3 scripts/lane.py LB03 RiffleLowerV2.Factorial.RelativeTargets
```

Log: `audit/LB03/ratios_build_dev10.log`, ending `LB03 BUILD_OK`. This builds all owned dependencies, including the actual exact and residual moment proofs, into the designated LB03 cache. Earlier successful numerical/scales log: `ratios_build_dev08.log`.

Independent source review by the mathematical reviewer approved the numerical implementation and exact-input discharge. The root's final lane-wide build and axiom-closure report are the authoritative complete-lane release record. There is no pending numerical theorem or dependency after the concrete build above.
