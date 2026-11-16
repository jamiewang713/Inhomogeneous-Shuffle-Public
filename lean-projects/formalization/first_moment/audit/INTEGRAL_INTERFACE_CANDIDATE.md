# Candidate one-sided integral/count interface

Status: statement-design review only, 2026-09-17. These are proposed supplemental statements, not frozen declarations or implemented Lean theorems. The original 29 first-moment interfaces are unchanged. The time-profile task is implementing the relevant route separately; this report does not duplicate that implementation.

I independently reread the authorized unified TeX's profile-cost definitions, almost-like condition, regular-partition and interval-blocking proof, and the maximal-pile, tail, and entropy replacement arguments. The source specifies a family of probability measures in time but no time-measurability hypothesis. The current Lean `TimeProfile.TimeLaw` likewise has no such field. Its integrated costs and almost-like cell integrals use totalized Lebesgue interval integrals.

The needed direction is that an integrated nonnegative cost is at most the empirical cost plus controlled errors. This direction suffices for all three original numerical premises. A two-sided approximation is unnecessary and cannot in general be obtained merely by adding totalized cell integrals.

## Core statement

The following signature uses the existing interval-integral notation and requires no new definitions. It could live in `TimeProfile`. Here `I i` is written inline as the existing totalized integral of `g i`.

```lean
theorem intervalIntegral_le_cellCount_bound
    {ι : Type*} [Fintype ι]
    (g : ι → ℝ → ℝ) (c x : ι → ℝ) (f : ℝ → ℝ)
    (a b M sigma : ℝ)
    (hab : a ≤ b) (hM : 0 ≤ M) (hsigma : 0 ≤ sigma)
    (hg : ∀ i t, t ∈ Set.Icc a b → 0 ≤ g i t)
    (hgsum : ∀ t ∈ Set.Icc a b, ∑ i, g i t = 1)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ M)
    (hx : ∀ i, 0 ≤ x i)
    (hf : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    (hupper : ∀ t ∈ Set.Icc a b,
      f t ≤ (∑ i, c i * g i t) + sigma) :
    (∫ t in a..b, f t) ≤
      (∑ i, c i * x i) +
      M * |(b - a) - ∑ i, x i| +
      M * (∑ i, |x i - ∫ t in a..b, g i t|) +
      sigma * (b - a)
```

The source nonnegativity of `f` is retained explicitly in this candidate; the core upper-bound proof can in fact avoid using it. It is needed in the endpoint corollary below. No `Measurable`, `AEStronglyMeasurable`, `IntegrableOn`, or `IntervalIntegrable` premise is present. Counts need not satisfy any exact normalization or approximation: both discrepancies are retained explicitly in the conclusion, to be bounded later from the original almost-like and floor facts.

The exact proof route uses a proof-local finite set

`G := {i | IntervalIntegrable (g i) volume a b}`.

Every integral with `i ∉ G` is zero by `intervalIntegral.integral_undef`. The function `q(t) := 1 - ∑ i ∈ G, g i t` is integrable on the interval and equals the sum of the bad cells there. In particular it is nonnegative, even though its individual summands need not be integrable. If `f` is nonintegrable its integral is zero and the displayed right side is nonnegative. If `f` is integrable, dominate it by the integrable function

`∑ i ∈ G, c i * g i t + M * q t + sigma`.

Writing `h = b-a` and `I_i = ∫ g_i` then gives

`∫ f ≤ ∑ c_i I_i + M * (h - ∑ I_i) + sigma*h`.

The exact finite identity behind the sharpened error is

`∑ c_i I_i + M*(h-∑ I_i)
 = ∑ c_i x_i + M*(h-∑ x_i) + ∑ (M-c_i)*(x_i-I_i)`.

Using `0 ≤ M-c_i ≤ M` gives the stated coefficient `M` on the coordinate error, without a factor of two. The deficit `h-∑ I_i` is not silently set to zero.

Trusted mathlib operations already available for this proof include `intervalIntegral.integral_undef`, `intervalIntegral.integral_mono_on`, `intervalIntegral.integral_finset_sum`, `intervalIntegral.integral_const`, `intervalIntegral.integral_const_mul`, `IntervalIntegrable.sum`, `IntervalIntegrable.sub`, `IntervalIntegrable.const_mul`, and `intervalIntegral.integral_nonneg`. Integrability is obtained only for proof-local majorants and through a case split, not imposed on the model.

## Actual empirical cost

Retain the exact hypotheses of the core statement and take an additional real `W` satisfying

```lean
(hW : |W - ∑ i, c i * x i| ≤ sigma * ∑ i, x i)
```

The proposed corollary `TimeProfile.intervalIntegral_le_empirical_bound` has conclusion

```lean
(∫ t in a..b, f t) ≤
  W + M * |(b - a) - ∑ i, x i| +
    M * (∑ i, |x i - ∫ t in a..b, g i t|) +
    sigma * ((b - a) + ∑ i, x i)
```

This adds only the already available finite representative-replacement estimate. It does not assume any new profile convergence or time integrability. If desired, its proof may be inlined at source instantiations rather than adding a second public theorem. A separate nonnegativity hypothesis on `W` is unnecessary.

For a grid interval, set `g i t = TimeProfile.cellMass mu P i t`, `x i = intervalCount ... i / logScale N`, and `sigma = C*chi`. The finite Borel partition gives pointwise nonnegative cell masses summing to one, with no measurability of `t ↦ mu t`. At each fixed time, integration in the simplex variable and regular-cell oscillation give the required pointwise upper bound. This uses only the existing probability-measure and Borel-partition structure.

The source cost choices are:

| Target | `f t` | `c i` | `M` | What the one-sided comparison supplies |
| --- | --- | --- | --- | --- |
| Maximal pile | `profileMaxCost mu t` | `maxCost (P.rep i)` | `log k` | `A(a,b) ≤ empiricalMaxCost + error`, hence the required upper bound for `cL` after subtraction. |
| Tail | `profilePsi mu t 2` | `psi (P.rep i) 2` | `4*log k` | `B₂(a,b) ≤ empiricalPsi₂ + error`, hence `cE ≤ -B₂ + error`. |
| Entropy | `profilePsi mu t theta`, `theta ∈ [3,4]` | `psi (P.rep i) theta` | `4*log k` | `Bθ(a,b) ≤ fullRepresentativePsiθ + error`; the existing exceptional-position deletion bound then gives `H ≤ theta*S - Bθ + error`. |

The bounds on `M` and representative costs are exactly `TimeProfile.maxCost_bounds` and `TimeProfile.psi_bounds`. The error bound for entropy is uniform in theta because the existing regularity oscillation and `4*log k` bound are uniform on `[2,4]`. One must use full cell counts for the comparison and then apply the exceptional-position deletion estimate; good-digit counts alone do not sum to the time interval length.

## Endpoint helper and source rounding

A useful additional candidate, if the time-profile implementation needs it, is:

```lean
theorem intervalIntegral_le_inner_add_endpoint
    (f : ℝ → ℝ) (a a' b' b M : ℝ)
    (haa' : a ≤ a') (ha'b' : a' ≤ b') (hb'b : b' ≤ b)
    (hM : 0 ≤ M)
    (hf : ∀ t ∈ Set.Icc a b, 0 ≤ f t ∧ f t ≤ M) :
    (∫ t in a..b, f t) ≤
      (∫ t in a'..b', f t) + M * ((a' - a) + (b - b'))
```

Again, no integrability hypothesis is required. If the larger interval's integral is nonintegrable it is zero and the right side is nonnegative. Otherwise its restrictions are integrable and ordinary integral additivity applies. The corresponding absolute-difference estimate is not valid without additional integrability and should not be substituted for this one-sided statement.

Apply the core comparison on the **original** positive-length almost-like grid intervals. For an arbitrary target interval, split on integrability of the target cost and use finite additivity only in the integrable branch, with the nonnegative endpoint bound above. Do not first claim arbitrary-interval cell-count equality by summing totalized cell integrals; that is the step the one-sided construction avoids.

The source horizon is exactly `K = floor(T * log N)`. The current `TimeProfile.Base` now includes

* `TimeProfile.horizonDepth N T := ⌊T * logScale N⌋₊`;
* `TimeProfile.horizonDepth_error`, assuming `2 ≤ N` and `0 ≤ T`, whose conclusion is `0 ≤ T - horizonDepth N T / logScale N < 1 / logScale N`;
* `TimeProfile.columnTime N j = (j.val + 1) / logScale N`.

Thus `T` must not be silently identified with `K / log N`. A final strip has cost at most `M / log N` using the one-sided endpoint lemma, or is retained in the explicit normalization discrepancy. The exact equality `K = horizonDepth N T` is a source-model instantiation fact, not a newly invented hypothesis replacing the original horizon.

There is another endpoint convention to preserve. `TimeProfile.intervalCount` uses the closed condition `a ≤ columnTime ≤ b`, whereas a tail after prefix length `m` uses `(m/log N, K/log N]`. At an exact gridpoint `a=m/log N`, the closed count can include one preceding column. Its contribution must be removed or budgeted, with total normalized count error at most `1/log N`. Adjacent closed almost-like grid intervals may also double-count a shared column; after fixing the number of grid blocks this contributes an explicit finite multiple of `1/log N`. Nonnegative costs make these finite corrections straightforward, but they cannot be discarded as exact identities.

The three candidate statements above are mathematical interfaces for further review. No supplementary statement has been frozen by this report, and no Lean implementation or original contract was edited.
