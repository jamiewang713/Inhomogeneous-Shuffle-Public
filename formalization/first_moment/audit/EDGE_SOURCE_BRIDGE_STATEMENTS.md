# Exact edge-to-source identities: statement candidate

Status: DESIGN ONLY. This candidate has one definition and ten exported theorems. No implementation or freeze exists. The primary agent designed the interfaces after reading the authorized article's finite block definitions and the actual project definitions. Independent algebra and adversarial reconstructions and exact reviews must be compared before implementation.

Proposed file: `FirstMomentModel/EdgeSourceBridge.lean`, namespace `InhomogeneousShuffle.FirstMoment.Model`. Imports include `FirstMomentModel.StableNumericalBridge`, `EdgeLocalization.Exponent.Model` and `EdgeLocalization.Collision.Rows`. The common runtime is Lean 4.33.1. The Edge compatibility copies preserve the incoming definitions and theorem types; their proof compatibility is audited separately.

These identities connect literal finite quantities. They neither assume nor assert a probability-law equivalence, endpoint estimate, localization theorem, horizon relation or asymptotic ambient normalization. The underlying count array is always `(asCuts D).count`, with the already proved column totals `(asCuts D).sum_count`.

## Definition

With implicit `D : Riffle.Model`, define exactly

```lean
def prefixVector (x : Riffle.Word) (hx : Riffle.Legal D x) :
    Fin x.length → Fin D.k :=
  fun t => legalVector x hx (Fin.castLE hx.1 t)
```

The domain is the actual word length. Padding in `legalVector` never enters this restriction. The existing model already gives `D.N>1`, `D.k≥2`, and nonnegative integer columns with the prescribed totals; no additional model field is introduced.

## Exhaustive theorem statements

All ten declarations have the common implicit variable `{D : Riffle.Model}`. No other variables are implicit beyond those printed in the definitions of existing types.

**ES1. Digit identity**

```lean
theorem prefixVector_digit (x : Riffle.Word) (hx : Riffle.Legal D x)
    (t : Fin x.length) :
    (prefixVector x hx t).val = Riffle.digit x t.val
```

**ES2. Literal word identity**

```lean
theorem prefixVector_word (x : Riffle.Word) (hx : Riffle.Legal D x) :
    EdgeLocalization.prefixWord (prefixVector x hx) = x
```

**ES3. Actual legal prefix**

```lean
theorem prefixVector_legal (x : Riffle.Word) (hx : Riffle.Legal D x) :
    EdgeLocalization.legalPrefix (asCuts D).count hx.1 (prefixVector x hx)
```

**ES4. Ambient coordinates**

```lean
theorem prefixVector_ambient (A : Riffle.Setup D)
    (x : Riffle.Word) (hx : Riffle.Legal D x) (hprefix : A.w <+: x)
    (t : Fin A.w.length) :
    prefixVector x hx (Fin.castLE hprefix.length_le t) =
      prefixVector A.w A.w_legal t
```

The ambient legality is the existing field `A.w_legal`. No duplicate legality, horizon or positivity premise is permitted. Equality of finite digits follows from equality of their natural values and proof irrelevance.

**ES5. Block-size exponent**

```lean
theorem edge_ambientSizeExponent_eq (A : Riffle.Setup D)
    (x : Riffle.Word) (hx : Riffle.Legal D x) :
    EdgeLocalization.ambientSizeExponent D.N (asCuts D).count hx.1
      A.w.length A.b (prefixVector x hx) = Riffle.cL A x
```

This exact finite-sum identity does not require `A.w <+: x`: if the lower length exceeds the upper length both sums are empty. The arbitrary exponent `A.b` is retained.

**ES6. Product mean and source mass**

```lean
theorem edge_prefixMean_source_eq (x : Riffle.Word) (hx : Riffle.Legal D x) :
    EdgeLocalization.prefixMean D.N (asCuts D).count hx.1 (prefixVector x hx) =
      TimeProfile.prefixMass D.N (asProfile D) (legalVector x hx) x.length
```

Both sides are expected populations, including the factor N. EdgeLocalization's `prefixMass` alone is a probability and must not be identified with TimeProfile's `prefixMass`.

**ES7. Product mean and actual weighted count**

```lean
theorem edge_prefixMean_expectedCount_eq
    (x : Riffle.Word) (hx : Riffle.Legal D x) :
    EdgeLocalization.prefixMean D.N (asCuts D).count hx.1 (prefixVector x hx) =
      (Riffle.expectedCount D (Riffle.Cylinder D x) : ℝ)
```

Use ES6 and the previously proved `expectedCount_cylinder_eq` at the reflexive prefix. No independent-column distribution is hypothesized to have this expectation.

**ES8. Signed ambient error**

```lean
theorem edge_ambientMeanError_eq (A : Riffle.Setup D) :
    EdgeLocalization.ambientMeanError D.N (asCuts D).count A.w_legal.1
      (prefixVector A.w A.w_legal) A.b =
        Real.log (Riffle.expectedCount D (Riffle.Cylinder D A.w) : ℝ) /
          Real.log (D.N : ℝ) - A.b
```

This is the literal signed discrepancy used by the existing `ambientApproximation_iff`. It is not set to zero and is not assumed nonnegative. In particular, for an empty ambient word its value is `1-A.b`; zero follows only when the separate data have `A.b=1`.

**ES9. One-column collision cost**

```lean
theorem edge_columnPsiTwo_eq (D : Riffle.Model) (j : Fin D.K) :
    EdgeLocalization.columnPsiTwo D.N ((asCuts D).count j) =
      TimeProfile.psi (asProfile D j) 2
```

Here D is explicit and replaces the common implicit D for this declaration. Zero pile coordinates are permitted; no full-support or positive-coordinate premise is added. The exponent on the left is the natural square, while the power sum on the right uses real exponent two.

**ES10. Tail exponent**

```lean
theorem edge_tailEdgeExponent_eq (D : Riffle.Model) (M : ℕ) :
    EdgeLocalization.tailEdgeExponent D.N (asCuts D).count M =
      TimeProfile.cE D.N (asProfile D) M
```

D is again explicit. M is every natural number, without `M≤D.K`. If M exceeds the horizon both sums are empty. This equality identifies the square-sum exponent, not the actual two-row factorial collision factor, for which the incoming theorem is an inequality.

## Exhaustive proof-local schemas

1. Restriction along `Fin.castLE` preserves the natural coordinate, and `legalVector_digit` applies because `t.isLt` gives the actual prefix bound. Extensionality of `Fin` handles proof irrelevance. `List.ofFn` reconstructs the original list from its in-range digits. ES3 uses the positive integer pile count in `hx.2`, not a claim that every padded suffix digit is legal.
2. `Riffle.digit_prefix hprefix` and ES1 give ES4. The length inequality used for its finite cast is derived from that same prefix relation. For ES5, reindex the finite sum over `t : Fin x.length` with `A.w.length≤t.val` to `Finset.Ico A.w.length x.length`; the summands agree by ES1 and the literal `asCuts.count` definition. No logarithm rule requiring additional positivity is needed for this sum identity.
3. For ES6, each `singleFactor` equals `TimeProfile.prob (asProfile D j)` at the same finite digit. Reindex the product over `Fin x.length` to `TimeProfile.positions D.K 0 x.length`; legality supplies `x.length≤D.K`. Multiplying both products by N gives the exact mean equality. The zero-length product is one on both sides, so the expected population is N. ES7 composes this with the already proved literal cylinder expected-count identity, and ES8 unfolds the existing signed-error definition and uses ES7 for the actual legal ambient word.
4. For ES9, identify each singleFactor with the existing profile probability, then use the trusted equality of the real power at natural exponent two and the natural square, including zero probabilities. Apply finite sum congruence and the same negated logarithm. No logarithm of an individual zero pile is used here.
5. For ES10, the Edge tail filter `M≤j.val` equals `TimeProfile.positions D.K M D.K`, since `j.isLt` supplies the upper bound. Rewrite every summand by ES9 and unfold `TimeProfile.logScale`. Empty horizons and out-of-range lower endpoints are included. The identity does not equate factorial two-row probabilities with squared one-row probabilities.

No additional definitions, helper exports, scientific assumptions or law-equality premises are proposed. Small-coarse and singleton density wrappers, ambient-relative edge semantics, actual horizon transport, source parameter instantiation, and large-block localization/density remain later integration obligations.
