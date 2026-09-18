# Independent implementation audit: T06–T08

## Verdict and reviewed versions

No mathematical defect, missing frozen conclusion, or assumption mismatch was found in the reviewed T06–T08 implementations. Every public theorem was compared with `FROZEN_TRUNCATION_CONTRACT.md`, its representation appendix, and the independently reconstructed proof routes in `truncation_reconstruction.md`.

Reviewed source hashes:

* `RiffleProfiles/ExceptionalTruncation.lean`: `073c5b711c8c94e08fc06b0a87d1d734db22c38890fc911a1720a7851b9cd84f`.
* `RiffleProfiles/MatrixLaw.lean`: `0a054b43828a0c9c7d0a6051525c9957be2abac39e8691ec33aa6d95f443da60`.

The MatrixLaw author confirmed that the latter version is final and compiles with `warningAsError=true`. T06 had already compiled under the same policy and its author had checked its transitive foundations. This audit was read-only: I did not modify either source or rebuild its output files. Compiler/kernel validation remains distinguishable from this independent mathematical and statement audit; the root agent is collecting the combined axiom reports.

A scan of both reviewed source files found no `axiom`, `sorry`, `admit`, or `opaque` declaration.

## T06: exceptional-prefix truncation

| Declaration | Audit |
|---|---|
| `sourceExceptionalDigits` (`ExceptionalTruncation.lean:19`) | The global bad-digit family is exactly the negation of the existing representative-good predicate, for each fixed column. It does not depend on the selected full word. |
| `sourceExceptionalPositions` (`:24`) | The literal exceptional filter on `positions K (v omega) (M omega)`. Both endpoint functions remain arbitrary full-word-dependent natural functions. |
| `sourceExceptionalPositions_subset` (`:30`) | Directly proves containment in the full-word bad-position set, without an ordering, legality, or positive-weight premise. |
| `sourceExceptionalDigits_prob_le` (`:39`) | Derives the exact bound `prob ≤ 3*chi` from the source regularity clause. No regularity result or digit bound is assumed in place of a proof. |
| `exceptionalPrefix_badCount_ge` (`:46`) | Retains `N ≥ 2` and `alpha ≥ 0`; multiplies the strict normalized event by positive `logScale N`, applies the nonnegative natural-floor equivalence, and composes with the proved cardinality inclusion. The threshold is exactly `Nat.floor (alpha*logScale N)+1`. |
| `exceptionalPrefix_wordMass_le` (`:65`) | Proves the exact finite indicator-sum bound under precisely the frozen regularity, positive-chi, `N ≥ 2`, and nonnegative-alpha premises. The right side is `tailWeight K (floor(alpha*L)+1) (k*(3*chi))`. |
| `exceptionalPrefix_scaled_wordMass_le` (`:102`) | Multiplies the same bound by the nonnegative real natural cast of `N`; it keeps all frozen premises and the factor `N`. |

The main proof applies the already proved F18 small-digit weighted tail to the fixed global bad-digit family. Coordinate nonnegativity and normalization come from the actual `TimeProfile.Simplex` values. Strict positivity of `3*chi` is derived from the frozen positive-chi assumption. Event inclusion is proved pointwise before comparing nonnegative sums; the proof does not count all high-exception patterns without their weights.

The endpoint functions can select a clipped, empty, or reversed interval and can depend on all digits. This does not affect containment in the full bad-position set. `alpha = 0` yields the correct threshold 1; `K = 0` gives an empty exceptional set and the strict event is impossible. A threshold larger than `K` is likewise impossible by the proved inclusion. Zero selected probabilities require no legality premise and contribute zero product weight. No actual selected-digit logarithm is used, so there is no total-real-logarithm substitution at zero.

The auxiliary per-digit theorem needs only the source regularity field because that field directly contains its conclusion; this does not remove the positive-chi premise from either frozen mass theorem. The whole-word weight remains exactly the existing `wordWeight`, with no independent-row law added.

## T07: actual uniform-column symmetry and marginals

| Declaration | Audit |
|---|---|
| Private `digitCount_permute` (`MatrixLaw.lean:19`) | Constructs the equivalence of digit fibres induced by the row permutation, proving preservation of the prescribed count. |
| `permuteFixedColumn` (`:26`) | A genuine equivalence of the same fixed-histogram outcome type; precomposition by the inverse permutation is proved inverse in both directions. |
| `columnLaw_permute_prob` (`:41`) | Proves invariance for every column event using the literal uniform-law formula and equal event-fibre cardinalities. Symmetry is not an extra premise. |
| `columnLaw_row_marginals_eq` (`:53`) | Applies that proved invariance to a transposition, giving equality of any two labelled-row digit marginals. |
| `fixedColumn_sum_indicator` (`:61`) | Proves the outcome-by-outcome real indicator sum equals the actual prescribed count. |
| `columnLaw_row_marginal` (`:73`) | Retains exactly `0 < N` for the empirical marginal formula; double counts the indicator sum and divides only after proving the real denominator nonzero. |

The permutation action's two inverse laws have the correct composition order: precomposition first by `e`, then by `e.symm`, evaluates the original function at `e(e.symm r)`, and conversely at `e.symm(e r)`. Thus event invariance refers to the actual uniform fixed-column law, not a different family of columns.

The marginal proof first establishes that the sum of row probabilities is `h.count a`, using the histogram equality in every outcome and the existing law's mass sum. It then uses the proved equality of row marginals to make that sum `N` times the chosen marginal. This handles `h.count a = 0` without any positivity premise for that digit. Histogram feasibility and nonemptiness come from the existing proved `Shuffle.fixedColumn_nonempty` construction, not from a new assumption.

The stronger-domain symmetry/indicator helpers are valid even when `N = 0`; the main marginal retains the frozen `N > 0` premise. No binomial distribution or independence between entries in a column is asserted.

## T08: actual matrix-row word law and expected cardinality

| Declaration | Audit |
|---|---|
| `modelHistogram` (`MatrixLaw.lean:106`) | Uses exactly the existing integer count at each finite column and digit. Its total is proved by converting the existing model sum into the finite-index sum. |
| `modelMatrixFintype` (`:112`) | Constructs the dependent-product enumeration using `Pi.instFintype` with classical index equality, matching the existing matrix-law representation. It is a fully constructed instance, not an additional hypothesis or a new sampling law. |
| `modelRowWord` (`:118`) | Extracts a labelled row of the actual dependent matrix as the existing `Riffle.FullIndex D`, with no sorting or relabelling. |
| `model_rowWord_probability` (`:123`) | Proves the exact full-word probability under the existing `Shuffle.fixedMatrixLaw (modelHistogram D)` equals `wordWeight (modelDigitProb D) omega`. |
| Private `model_rowWord_event_probability` (`:144`) | Uses the existing finite pushforward and proved atom probabilities to obtain the exact finite indicator sum for an arbitrary natural-word event. |
| `model_expected_row_count` (`:163`) | Proves the real expected cardinality of the actual labelled-row event equals the existing NNReal `expectedCount` coerced to Real, for every set of natural-number words. |

The row-word equality event is proved equivalent to the coordinate rectangle by function extensionality. The matrix law unfolds to the existing product of actual uniform-column laws. The explicit call to `product_prob_rectangle` supplies exactly those column laws and the events that a fixed row has its prescribed digit. T07's marginal formula then gives the coordinate ratios and hence the full product weight. This argument uses only independence of columns already built into the existing law.

The expected-cardinality proof expands the finite row count into indicators, exchanges finite summations, substitutes the proved row-event probability, and sums the identical marginal across `Fin D.N`. This produces exactly the factor `D.N` in `model_expectedCount_eq_wordMass`. It makes no independence assertion about different rows. It also does not require an event to consist solely of legal words: impossible full words have zero marginal, and words of other lengths never occur as the extracted full row.

The dependent Fintype elaboration adjustment is confined to choosing the standard product enumeration. It neither changes the coordinates in `modelHistogram` nor replaces `fixedMatrixLaw` with a newly postulated law. I rechecked the final explicit product-rectangle invocation after the author reported its compiler fix; the reviewed hash above includes that change.

The existing imported definitions were also checked at their actual vendored paths: `Histogram`/`FixedColumn` and the feasibility proof, `columnLaw = uniform`, `FiniteLaw.uniform_prob`, `FiniteLaw.product`, its rectangle theorem, and `fixedMatrixLaw = product columnLaw`. These provide the concrete distributional content required by T07–T08.

## Scope and remaining obligations

T06 is fully covered by the exact exceptional filter, event implication, weighted tail, and scaled corollary. T07 is fully covered by the explicit permutation equivalence, invariance for arbitrary events, equality of marginals, count identity, and empirical marginal formula. T08 is fully covered by the exact model histograms, row extraction, full-word probability, and actual expected row cardinality identity.

These modules leave the frozen boundaries of the work intact: no time measurability or integral estimate, negative-power asymptotic conclusion, sorted-graph edge bound, exceptional-profile class counting claim, or terminal-exemption policy is asserted. The distinction between one-row product distribution and dependent rows is correctly preserved throughout.
