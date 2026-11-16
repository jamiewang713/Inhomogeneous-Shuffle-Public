# T07–T08 implementation and validation

Implemented `RiffleProfiles/MatrixLaw.lean` under namespace
`RiffleProfiles`, after reading `FROZEN_TRUNCATION_CONTRACT.md` and
`TRUNCATION_REVIEW_COMPARISON.md`. The frozen contract SHA256 is
`d1cd3287aa31cb0b3236c9cf811399a63a648b435d299cfaa0dbd789e2406a66`.
No other Lean source, original dependency, or contract was edited by
this implementer.

Final module SHA256:
`0a054b43828a0c9c7d0a6051525c9957be2abac39e8691ec33aa6d95f443da60`.

The module compiles with the pinned Lean 4.19.0/mathlib environment using
`python3 lean_formalization/check_lean.py lean_formalization/RiffleProfiles/MatrixLaw.lean`.
The final check returned exit zero with `warningAsError=true` and no
diagnostics. The implementation's own style linters were not disabled.

## T07 coverage

| Declaration | Exact data and conclusion |
|---|---|
| `permuteFixedColumn` | For `h : Shuffle.Histogram (Fin N) k` and `e : Equiv.Perm (Fin N)`, an equivalence `Shuffle.FixedColumn h ≃ Shuffle.FixedColumn h` whose forward map is row precomposition by `e` |
| `columnLaw_permute_prob` | For every event `E : Shuffle.FixedColumn h → Prop`, the probability of `E (permuteFixedColumn h e f)` equals the probability of `E f` under the existing `Shuffle.columnLaw h` |
| `columnLaw_row_marginals_eq` | For any `r s : Fin N` and `a : Fin k`, `P(f.val r = a) = P(f.val s = a)` |
| `fixedColumn_sum_indicator` | In every actual column outcome `f`, `∑ r, if f.val r = a then (1 : ℝ) else 0 = (h.count a : ℝ)` |
| `columnLaw_row_marginal` | With precisely `hN : 0 < N`, any row `r` and digit `a` have probability `(h.count a : ℝ) / (N : ℝ)` |

The private `digitCount_permute` proves invariance of the digit count by
an equivalence of its row fibres. Thus the permutation equivalence
preserves the existing histogram, rather than changing its counts.
Uniform event invariance follows from the corresponding event-fibre
cardinality equivalence. A row transposition gives equal marginals.
Summing those marginals and exchanging two finite sums gives the exact
histogram count; division occurs only after using `N > 0`.

These are proofs of the symmetry and marginal facts, not hypotheses.
The final marginal requires no positive count for the selected digit.
Zero counts give probability zero. The intermediate symmetry statements
also cover an empty row type; the final marginal retains its frozen
positive-`N` premise.

## T08 coverage and exact interfaces

`modelHistogram (D : Riffle.Model) (j : Fin D.K)` has type
`Shuffle.Histogram (Fin D.N) D.k`, with the literal count function
`a ↦ D.n j.val a.val`. Its total is proved from `D.sum_counts`.

`modelRowWord (D : Riffle.Model)
  (matrix : ∀ j : Fin D.K, Shuffle.FixedColumn (modelHistogram D j))
  (r : Fin D.N)` has type `Riffle.FullIndex D` and value
`j ↦ (matrix j).val r`.

`model_rowWord_probability (D : Riffle.Model) (r : Fin D.N)
  (ω : Riffle.FullIndex D)` proves exactly

`(Shuffle.fixedMatrixLaw (modelHistogram D)).prob
  (fun matrix => modelRowWord D matrix r = ω)
  = wordWeight (modelDigitProb D) ω`.

`model_expected_row_count (D : Riffle.Model) (E : Set Riffle.Word)`
proves exactly

`(Shuffle.fixedMatrixLaw (modelHistogram D)).expect
  (fun matrix => ((Finset.univ.filter (fun r : Fin D.N =>
    Riffle.fullList (modelRowWord D matrix r) ∈ E)).card : ℝ))
  = (Riffle.expectedCount D E : ℝ)`.

The first proof identifies function equality with the rectangular event
specifying each column's digit in a fixed row. It invokes the existing
`Shuffle.FiniteLaw.product_prob_rectangle`, applies the proved T07
marginal to each column, and identifies the resulting real ratios with
`modelDigitProb D`. The law is exactly the existing
`Shuffle.fixedMatrixLaw (modelHistogram D)`.

The private `model_rowWord_event_probability` derives the probability
of any list event from the already proved word atoms using the existing
finite pushforward. The final proof expresses the row cardinality as a
sum of indicators, exchanges finite sums, and uses that event marginal
for every row. It then invokes T01's
`model_expectedCount_eq_wordMass` to identify the original `NNReal`
functional after coercion to the reals.

`E` is arbitrary: no legality, support, measurability, or probability
premise is imposed on it. Zero-count digits and empty column index sets
are covered by the finite products and sums. No independence of
different rows is asserted or used.

## Dependent finite-instance compatibility

Lean 4.19 exposes a definitional instance mismatch when applying the
existing generic `fixedMatrixLaw` to the concrete index type `Fin D.K`.
The law's dependent-product `Fintype` was constructed using classical
equality on its generic column index. Default inference at `Fin D.K`
instead selects the computable equality instance, producing a
definitionally different dependent `Fintype` term.

The module provides the specialized instance
`modelMatrixFintype (D : Riffle.Model)` for exactly
`∀ j : Fin D.K, Shuffle.FixedColumn (modelHistogram D j)`.
It uses `Pi.instFintype` with the same classical index equality as the
existing law. This instance is registered at priority 2000 so consumers
of the T08 theorems infer the matching finite matrix type as well.
It introduces no theorem hypothesis, new sample outcomes, altered law,
or probabilistic assumption. No dependency source required a patch.

## Trusted-dependency check and limits

A separate `#print axioms` check imported the final compiled module and
examined all six public theorems plus `permuteFixedColumn`,
`modelHistogram`, `modelMatrixFintype`, and `modelRowWord`. Every result
reported exactly `[propext, Classical.choice, Quot.sound]`; the check
returned exit zero. The check and output are retained at
`/private/tmp/riffle-matrix-law-axioms.lean` and
`/private/tmp/riffle-matrix-law-axioms.log`.

There are no `axiom`, `sorry`, `admit`, or unproved declarations in the
module. The proofs use only the frozen object data, reviewed finite
counting/symmetry routes, proved project facts, and trusted mathlib
results. T07–T08 are complete at these finite statements. Sorting rows,
shuffle-graph edges, row independence, and ordered-limit estimates are
outside their conclusions. T09 is a separate application by the
coordinator.
