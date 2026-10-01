# LB06 independent implementation review: Truncation v1

Reviewed source: `RiffleLowerV2/Types/Truncation.lean`, 847 lines, SHA-256
`43f19d9366f2cc8608da41158d38be6b1d2d6f115509ccd7857fba828bfea346`.
The reviewer did not author or modify this source. The review checks the
mathematics, exact hypotheses, zero coordinates, tilt interval, and uniformity
of its implementation against `lem:type-estimates` and Contracts/v1.

Verdict: approved. No false premise, hidden positivity assumption, target-like
assumption, or unplanned dependence on LB05 was found. No change is requested.

## Denominators, support, and endpoint cases

`exists_prob_ge_inv_card` uses simplex normalization to find a coordinate at
least 1/k. `cutoff_small` proves xi<1/8 and 2xi<1/k from k≥2 and
0<xi<1/(4k). Consequently a representative always has a retained coordinate.
`retainedTilt_denominator_pos` works for every real alpha, since that coordinate
is strictly positive. The normalized retained law is not inferred from Lean's
totalized division: `retainedTilt_sum` explicitly uses the proved nonzero
denominator.

For an actual p in the representative cell, `restrictedSum_pos` uses the
regularity field `good_digit` to prove positivity of the corresponding actual
coordinate. `retainedTilt_nonneg`, zero-on-omitted, positivity-on-retained, and
the bound by one are proved explicitly. No coordinate outside the retained
support is divided by or passed through a positive-log rewrite.

Full tilted weights are used only under alpha∈[2,4]. In
`tiltedEntropy_identity` and `tiltedEntropy_term_bounds`, a nonzero tilted
weight implies a positive original coordinate; the zero-coordinate case uses
alpha≠0, which follows from alpha≥2. Thus `Real.log 0 = 0` and totalized real
powers do not create spurious entropy contributions.

The support convention is consistent: retained means `2*xi < prob r l`, and
omitted means `prob r l ≤ 2*xi`. Equality belongs to the omitted part. Actual
omitted coordinates are bounded by 3xi using the regularity hypothesis.

## Uniform estimates and constants

The coarse lower bound

```text
1 ≤ k^4 * powerSum(p,alpha)
```

comes from one coordinate at least 1/k and alpha≤4. The same bound holds for
the retained representative denominator because that coordinate is retained.
It is uniform over the entire closed simplex, including boundary points, and
over alpha∈[2,4]. No continuity compactness argument is used to conceal a
point-dependent lower bound.

The omitted estimates are explicit:

| Quantity | Proved bound |
| --- | --- |
| Omitted full tilted mass | `9*k^5*xi^2` |
| Omitted full tilted cost | `12*k^5*xi^2*log(1/xi)` |
| Omitted full tilted entropy | `48*k^5*xi^2*log(1/xi)` |

The sharper cost estimate `power_digitCost_small` handles p=0 separately.
For p>0 it writes log(1/p)=log(1/xi)+log(xi/p), applies log(t)≤t−1, and
uses p≤3xi and log(1/xi)≥1. This is a valid alternative to proving monotonicity
of x²log(1/x). The entropy estimate uses

```text
0 ≤ -q_l log q_l ≤ 4*q_l*digitCost(p_l)
```

with the q_l=0 branch explicit; its upper bound follows from alpha≤4 and
log(powerSum)≤0. The omitted set need not be the support of a probability law.

Earlier coarser O(xi) omitted-cost estimates remain in the proof of the final
retained-cost transfer. This is mathematically sufficient because the required
final budget is O(xi log(1/xi)) and log(1/xi)≥1. The sharper source-scale
omitted-cost and omitted-entropy bounds are additionally checked exports;
their availability is not confused with a stronger final error claim.

## Transfer to actual columns

`powers_close` obtains unnormalized power ratios exp(±4Cxi) from the regular
cell log-cost bound. `normalized_le` compares positive denominators and gives
the normalized ratios exp(±8Cxi). `abs_sub_le_of_ratios` correctly converts the
two ratio inequalities into an error bounded by `(exp(8Cxi)-1)*q_actual`.

The passage to `8*C*exp(C)*xi` uses xi≤1/8 and C≥0. It does not assume Cxi is
small or assume C is bounded independently of its quantifier. Dependence on
exp(C) is allowed because the target chooses C before its approximation
constant and before xi.

Retained actual digit costs are between zero and log(1/xi). Thus the weighted
ratio error sums without a factor depending on the particular representative,
actual point, or retained support size. Representative-to-actual cost
replacement adds Cxi and uses actual normalization of the retained law.

The final constants are named:

```text
truncationCostConstant(k,C) = C + 8*C*exp(C) + 18*k^5
truncationEntropyConstant(k,C) =
  4*truncationCostConstant(k,C) + 4*C + 9*k^5.
```

`retainedTilt_cost_transfer` and `retainedTilt_entropy_transfer` bound their
respective absolute errors by the named constant times xi*log(1/xi). These
constants depend only on k,C. They are independent of xi, alpha, the number of
cells, the partition, the actual cut array, the selected column set, and N.

Entropy transfer proves the entropy/cost/log-normalizer identity from the
actual Shannon-entropy definition. It bounds representative truncation of the
normalizer directly and then uses `P.IsRegular.psi_oscillation` for the full
representative/actual normalizers. This uses exactly an existing regularity
field, and introduces no macroscopic approximation for tilted cost or entropy.

## Dependency and trust audit

The source imports only `RiffleLowerV2.Shared.Geometry`. Its generic helpers
accept elementary positivity, normalization, and support conditions; every
such premise is discharged in the concrete retained-law transfer theorems from
the stated simplex and regularity hypotheses. No helper assumes the desired
transfer or final TypeApproximation.

The reviewer independently imported the compiled Truncation module under the
pinned Lean 4.33.1 runtime and printed axiom closure for:

* `retainedTilt_denominator_pos`
* `retainedTilt_sum`
* `tiltedEntropy_identity`
* `omittedTiltedSum_le`
* `omittedTiltedCost_small`
* `omittedEntropySum_bounds`
* `retainedTilt_cost_transfer`
* `retainedTilt_entropy_transfer`

All eight commands succeeded; each closure is exactly `propext`,
`Classical.choice`, and `Quot.sound`. The compiled Truncation artifact was newer
than the reviewed source. This check does not substitute for the source-level
uniformity and support review above.

No unresolved analytic issue remains for the reviewed source version.
