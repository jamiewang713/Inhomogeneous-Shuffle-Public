# LB03 Bonferroni and scalar comparison delivery v1

## Verified build

From `formalization/lower_bound_v2`:

`python3 scripts/lane.py LB03 RiffleLowerV2.Factorial.PoissonPolynomial`

Result: `LB03 BUILD_OK`, recorded in `audit/LB03/bonferroni_build_v5.log`. The lane driver compiled both `Factorial/Bonferroni.lean` and `Factorial/PoissonPolynomial.lean` against the pinned shared dependency cache and checked the immutable contracts before compilation. Earlier v1–v4 logs are development diagnostics, not completion receipts.

## Completed exports

- `RiffleLowerV2.Factorial.bonferroniSandwich : RiffleLowerV2.Targets.BonferroniSandwich`.
- `RiffleLowerV2.Factorial.bonferroniProduct : RiffleLowerV2.Targets.BonferroniProduct`.
- `RiffleLowerV2.Factorial.poissonPolynomial (m : ℕ) (t : ℝ) : ℝ`, defined by the signed finite sum from 2 through m.
- `RiffleLowerV2.Factorial.poissonPolynomial_sandwich (m : ℕ) (hm : 2 ≤ m) (heven : Even m) (t : ℝ) (ht : 0 ≤ t)` proves `0 ≤ poissonPolynomial m t - poissonCollision t` and that this difference is at most `poissonRemainder m t`.
- `RiffleLowerV2.Factorial.poissonCollision_bounds (t : ℝ) (ht : 0 ≤ t)` proves `0 ≤ poissonCollision t ∧ poissonCollision t ≤ 1`.
- `RiffleLowerV2.Factorial.poissonCoefficientSum_le (m : ℕ) (t : ℝ) (ht : 0 ≤ t)` bounds `Σ_(r∈Icc 2 m) (r−1)t^r/r!` by `(1+t)exp(t)`.
- `RiffleLowerV2.Factorial.product_remainder (u v a b dx dy : ℝ)` proves `0≤uv−ab≤dx+dy+dx*dy` under `0≤a≤1`, `0≤b≤1`, `0≤u−a≤dx`, and `0≤v−b≤dy`.

The compiled supporting exports `hasSum_poissonWeight`, `hasSum_poissonWeight_choose`, `hasSum_poissonWeight_indicator`, `hasSum_poissonWeight_bonferroni`, and `hasSum_poissonWeight_remainder` certify every infinite-series identity used by the scalar comparison.

## Source and mathematical correspondence

The pointwise bounds implement the displayed Bonferroni sandwich and product remainder in `lem:central-window`. An exact positive binomial remainder is proved by induction using Pascal's identity; n=0, n=1 and m=2 are included. The argument never removes a large-count event.

For the scalar benchmark the implementation uses a second exact route considered alongside the review's Taylor route. It defines scalar exponential weights `exp(−t)t^n/n!`, proves normalization directly from the trusted exponential series, and proves each weighted binomial moment by factorial cancellation and shifting the series. It then sums the pointwise Bonferroni bounds over **all** natural counts. Thus no approximation, independence law, or desired factorial moment is added as a hypothesis. This also avoids instantiating finite `expect` on an infinite sample space.

Every prerequisite scalar series is proved summable as part of a `HasSum` statement before order comparisons are used. The coefficient sum is bounded by the nonnegative exponential series after the exact identity `Σ_(r≤m) r t^r/r! = t Σ_(r<m) t^r/r!`.

The code imports no sibling implementation lane and changes no frozen statement. The scalar comparison has an explicit nonnegative t premise; the frozen central targets have positive means and therefore satisfy it.

## Development issue resolved

The first scalar draft left the unshifted function implicit in `HasSum.sum_range_add`, requiring difficult higher-order unification from its shifted form. Supplying explicit `f` and `k` solved both heartbeat timeouts; increasing the heartbeat limit alone had not solved them. No mathematical premise or conclusion was changed.

## Scope of this receipt

This certifies the two owned files and the two frozen pointwise targets, plus the scalar helpers consumed by the central comparison. It does not certify the root's central assembly before its own build, or the exact/residual factorial lanes. A separate independent implementation review and a complete lane axiom-closure report remain coordinator obligations.
