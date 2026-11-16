# LB05 empirical interpolation implementation receipt, version 1

Date: 2026-10-01. Implementer: `lb05_math_review` following the coordinator's additional implementation assignment after completing the independent mathematical review.

## Checked public target

```lean
RiffleLowerV2.Witness.empiricalTilt :
  RiffleLowerV2.Targets.EmpiricalTiltTarget
```

Its expanded frozen type is:

```lean
∀ k N K : ℕ, 2 ≤ k → 2 ≤ N →
∀ (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
∀ alpha ∈ Set.Icc (2 : ℝ) 4, ∀ r s : ℝ,
0 ≤ r → r ≤ s → s ≤ RiffleLowerV2.horizon N K →
0 ≤ RiffleLowerV2.J cuts hN alpha r s ∧
RiffleLowerV2.J cuts hN alpha r s ≤ (s-r)*Real.log k ∧
0 ≤ RiffleLowerV2.H cuts hN alpha r s ∧
RiffleLowerV2.H cuts hN alpha r s ≤ RiffleLowerV2.J cuts hN alpha r s ∧
RiffleLowerV2.H cuts hN alpha r s =
  alpha*RiffleLowerV2.J cuts hN alpha r s - RiffleLowerV2.B cuts hN alpha r s
```

`empiricalTilt` discharges the generic helper's one-column input with the separately checked concrete `oneColumnTilt`. No witness, endpoint conclusion, macroscopic profile, temporal regularity, or empirical bounds are assumed by this public theorem.

## Imports and helper exports

Import `RiffleLowerV2.Witness.Empirical` for the independently compiled generic finite interpolation toolkit. Import `RiffleLowerV2.Witness.EmpiricalTilt` for the concrete target and specialized helpers; it transitively imports the checked one-column implementation. All helper names below are in `RiffleLowerV2.Witness`.

The generic module proves:

- `columnFraction_mono`, `columnFraction_sum`: monotone fractions and exact total `t*logScale N` on the empirical horizon.
- `empiricalIntegral_const`, `empiricalIntegral_linear`, `empiricalIntegral_swap`: exact constants, linearity, and oriented reversal.
- `empiricalIntegral_mono`, `empiricalIntegral_nonneg`, `empiricalIntegral_le`: integrand comparison and the sharp interval bound `(s-r)*M`.
- `empiricalIntegral_abs_le`, `empiricalIntegral_endpoint_bound`: oriented absolute bounds and `(abs(r-r')+abs(s-s'))*M` endpoint error, for endpoints in the empirical horizon and pointwise `abs(f j)<=M`.
- `continuous_columnFraction`, `continuous_empiricalIntegral`, `continuousOn_empiricalIntegral_param`: global endpoint continuity and finite-sum parameter continuity.

Exact grid sums and additivity are reused from the checked shared foundation as `RiffleLowerV2.empiricalIntegral_grid` and `RiffleLowerV2.empiricalIntegral_add`; no duplicate temporal interpolation was introduced.

The specialized module proves `A_bounds`, `J_bounds`, `H_bounds`, `B_bounds`, `H_identity`, `A_le_J`, `B_two_le_A`, `B_two_le_J`, `B_four_ge_two`, `continuousOn_J_alpha`, `continuousOn_B_alpha`, `continuousOn_H_alpha`, `antitoneOn_J_alpha`, `continuous_J_time`, `continuous_B_time`, `continuous_H_time`, and `A_endpoint_bound`, `J_endpoint_bound`, `B_endpoint_bound`, `H_endpoint_bound`.

For modular proof assembly, the tilted specialized helpers and `empiricalTiltFrom` explicitly accept the entire one-column toolkit proposition as an input. Their callers supply the checked `oneColumnTilt`; they are generic deduction lemmas, not replacements for the completed concrete `empiricalTilt` export. `A_bounds` and `A_endpoint_bound` directly use the checked one-column max-cost bounds and have no such input.

## Source correspondence and proof status

These declarations formalize the empirical step interpolation and integrated toolkit preceding `lem:cold-witness` and the endpoint error estimates used inside its proof. All work uses the exact frozen `columnFraction`, `empiricalIntegral`, A/B/J/H, and cut profiles. The total-weight calculation telescopes the clipped primitive; it therefore has no integration or regularity assumptions.

| Component | Status |
|---|---|
| Generic fraction weights, interval bounds, continuity, linearity | Checked |
| Sharp integrated one-column toolkit | Checked |
| Actual target `empiricalTilt` | Checked |
| One-column input | Checked by separate implementation and transitively rebuilt |
| Full continuous/grid witness | Coordinator and rounding agent assembly; not claimed by this receipt |

## Verification

Final command from the package directory:

```text
python3 scripts/lane.py LB05 RiffleLowerV2.Witness.EmpiricalTilt
```

The final output is exactly `LB05 BUILD_OK`, with no warnings. The preserved log is `audit/LB05/empirical-build-final-v1.log`. Earlier development logs remain separate.

The source-only check `audit/LB05/EmpiricalCheck_v1.lean` was run against the lane output with the pinned Lean runtime. The log `audit/LB05/empirical-axioms-v1.log` confirms exactly `[propext, Classical.choice, Quot.sound]` for `empiricalTilt`, the generic endpoint bound and joint continuity, and both integrated psi comparisons. The subsequent changes only removed two linter warnings and did not change declaration types or proof content.

No frozen contract, shared module, manuscript, Lake configuration, dependency cache, original package, or old freeze record was edited.
