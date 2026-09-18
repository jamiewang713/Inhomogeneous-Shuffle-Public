# Exact stable/numerical bridge: independent algebra review

## Approval

I approve the four definitions and all sixteen SN1–SN16 interfaces in `audit/STABLE_NUMERICAL_BRIDGE_STATEMENTS.md`, SHA-256

`05f5f072fb6d7061e85f4167dbe9566f6a3648a3729422f29b6e761a9ccb2138`.

This includes the explicit `(D := D)` in SN6. No mathematical assumption, binder, conclusion, or definition requires correction. No extra hypothesis is needed for the finite expectation identities, the empty-range cases, or the prefix/parent statements. This is a pre-freeze reconstruction and statement review, not an implementation or a claim that the sixteen proofs have been checked.

I reread the actual project definitions and prerequisite theorems, rather than identifying expressions only by their informal meaning. The source comparisons use the unified TeX's ambient definition at lines 490–518, boundary/side/stable definitions at 521–696, fluctuation comparison at 965–994, and parent-crossing argument at 998–1007. These are finite consequences of those definitions; neither a homogeneous cutoff constant nor a new stochastic anti-concentration claim is involved.

As a separate type check, all sixteen displayed proposition signatures elaborated under Lean 4.33.1 with the four adapter types supplied as local parameters. This check used only transient `#check` expressions, not declarations, axioms, placeholders, or proof implementations. In particular the integral, `Full` application, dependent legality arguments, and `hx.1.1.1` projection have the stated types. The nondependent hypothesis warnings from these proposition-valued lambdas have no mathematical significance.

## The four definitions

- **D1, `asCuts`: approved.** `Cuts.count` expects exactly `Fin K → Fin k → ℕ`; the proposed projection to `D.n` has that type. Reindexing the finite alphabet sum proves `sum_count` from `D.sum_counts`. All queried columns and digits are within the ranges governed by `Riffle.Model`. For `K=0` the sum field is vacuous.
- **D2, `asProfile`: approved.** The profile is the already defined count-over-`N` simplex. `0 < N` follows from `D.one_lt_N`. It introduces neither a changed pile sequence nor an additional probability law. Differences between proofs of this positivity premise are irrelevant.
- **D3, `legalVector`: approved.** On the actual word, `hx.2 j hj` supplies the alphabet bound and positive count. Beyond its length, `0 < k` follows from `D.two_le_k`, so padding by zero defines a total alphabet-valued vector. No positive probability for that padding is needed. Every theorem that reads actual coordinates restricts to positions before a legal prefix length.
- **D4, `sideProbability`: approved.** Case analysis on `Riffle.Side` selects the existing left or right sum, with the exact strict digit inequalities in the source. The definition is meaningful for every natural `k`; the model applications already have `k≥2`.

These definitions retain the existing `A.b`, absolute list lengths, actual ambient word, and original model. `A.C` remains the boundary-budget constant. There is no horizon, ambient approximation, time law, or partition added to this finite adapter contract.

## Reconstruction of SN1–SN16

### SN1: probability coordinates

Unfold `asProfile`, use `Cuts.profile_prob`, and unfold `Riffle.prob`. Coercion of NNReal division and natural casts gives

`prob (asProfile D j) l = (D.n j.val l.val : ℝ) / D.N = (Riffle.prob D j.val l.val : ℝ)`.

Zero pile counts are included. No legality premise on the digit is necessary.

### SN2: actual digit of the vector

The supplied `hj` selects the first branch of D3. The value of the resulting `Fin` is exactly `Riffle.digit x j.val`. No claim is made about the padded suffix.

### SN3: legal prefix

For `j.val < x.length`, SN2 gives the actual digit. `hx.2` gives its positive natural count; `Cuts.profile_pos_iff` transfers this to positive profile probability. `LegalPrefix` is precisely this pointwise positivity assertion. The word-length bound is already part of `hx`; it need not be repeated as a premise.

### SN4: cost of every represented prefix

For every `u <+: x`, derive `u.length ≤ x.length ≤ K`. The map `j ↦ j.val` bijects `positions K A.w.length u.length` with the natural `Ico A.w.length u.length`. At every included index, `Riffle.digit_prefix` and SN2 identify the digits. SN1 and the field identity

`1 / ((n : ℝ) / (N : ℝ)) = (N : ℝ) / (n : ℝ)`

identify each logarithmic summand. The denominator `logScale N` is `Real.log (N : ℝ)`. Both sides retain exactly `A.b`.

There is deliberately no `A.w <+: u` premise: if `u.length < A.w.length`, both index sets are empty and both literal costs equal `A.b`. If the interval is nonempty, its indices still lie before `u.length`, which is all that the algebra needs. Thus this modest generality is valid and does not assume an ambient mass identity.

### SN5: parent cost

Apply SN4 to `Riffle.parent_prefix x` and rewrite `Riffle.parent_length`. The vector is still the one encoding `x`, so no equality between differently padded vectors is presumed. Natural subtraction handles the empty word: its parent has length zero and the equality remains valid.

### SN6: actual sample rows are full legal lists

`Riffle.fullList_length` supplies length `K`, and each coordinate has alphabet bound by its `Fin k` type. `TimeProfile.sample_entry_count_pos sample i j` gives positivity of the count in D1. Rewriting the digit by `Riffle.fullList_digit` establishes list legality and hence `Full`.

This is a statement about an actual fixed-count sample. An arbitrary alphabet-valued vector can use a zero pile and is not covered. The explicit `D` annotation identifies exactly the intended list representation.

### SN7: literal expectation equality for every set of words

For a full finite vector `ω`, let its singleton-coordinate box use `{ω j}` in every column. Its row set is exactly the rows whose complete vector equals `ω`. For each sample, the following finite identity holds:

`rowCount(E) = ∑ ω, if fullList ω ∈ E then singletonBoxCount(ω) else 0`.

Indeed every row has one and only one complete finite vector, so its indicator appears once. Integrate this finite sum. `fixedCount_integrable` applies to every real function on the existing finite sample space, including each summand for an arbitrary set `E`. `expected_box_count` evaluates the singleton box to `N * ∏ j, prob (asProfile D j) (ω j)`. SN1 and NNReal coercion of finite sums/products then recover exactly `Riffle.expectedCount D E`.

No measurability premise on `E` is missing: the relevant vector and sample spaces are finite, and the fixed-count space has the discrete measurable structure. This argument does not assert independence between rows. It uses the already proved fixed-column law for one row's box and then linearity. For `K=0`, the vector space is a singleton, both sides count all `N` rows precisely when `[] ∈ E`, and the empty product is one.

### SN8: cylinder expectation

By prefix legality, `u.length ≤ K`. On each actual sampled row SN6 supplies `Full`. Then

`fullList row ∈ Cylinder D u`

is equivalent to coordinate agreement with `legalVector x hx` before `u.length`: digit agreement uses SN2 and `digit_prefix`, and the converse reconstructs the list prefix using the known lengths. Thus the row count in SN7 is exactly `(prefixRows ... u.length sample).card`. Apply `expected_prefix_count`, with the derived length bound.

The predicate equivalence is required only on sampled rows. It is generally false on arbitrary raw vectors unless the zero-weight illegal case is separately handled. The proposed interface does not make that false assertion.

### SN9: side-piece expectation

The premises give `A.w.length ≤ j.val < x.length ≤ K`. On sampled rows, `Riffle.pieceEvent_iff` supplies the exact conjunction of the ambient cylinder, agreement before `j`, and the strict left/right digit comparison. Because `x` extends `A.w` and `j` is beyond the ambient prefix, agreement before `j` already forces that ambient prefix. SN6 supplies legality; SN2 identifies the compared digit. Hence the event equals `leftSideRows` or `rightSideRows` on each sample. SN7 and the corresponding existing expected-side-count theorem yield the displayed mass formula.

This proof leaves every later column unrestricted, as the definitions require. It takes no conditional law as a premise and asserts no conditional variance. Empty sides and zero pile counts are included.

### SN10: finite maximum of the same side expectations

From `hvx`, derive `v.length ≤ x.length ≤ K`. Reindex `Ico A.w.length v.length` to `positions K A.w.length v.length`. Each index meets the two range premises of SN9. Its expected count agrees with the corresponding side mass. These quantities are nonnegative; equivalently `Real.toNNReal` of the real coercion of the NNReal expected count recovers that expected count. Therefore the two finite NNReal suprema, and their real coercions, agree.

If `v.length < A.w.length`, both index sets are empty and both maxima are zero. No ambient-prefix premise on `v` is missing. This is a maximum of expectations throughout; expectation is never commuted with a random maximum.

### SN11: extended fluctuation exponent

Use SN10 on both sides, take the same real square roots, and unfold the two extended logarithms. `Riffle.extendedLog` and `TimeProfile.logExponent` have identical zero tests and equal denominators. Their minimum therefore agrees in `WithBot ℝ`. Empty or zero side maxima yield bottom on both sides, rather than an ordinary real zero.

### SN12: boundary-pair representative

`rawPair_join_desc hp` gives the ambient prefix relation for the join. Combining it with `hx.2` proves `x ∈ Desc D A.w`. The existing `cFAt_continuation` identifies the fluctuation computed with continuation `x` with that computed at the join itself, which is the definition of `Riffle.cF`. SN11 then proves the displayed equality. Proof irrelevance handles the two proofs of legality passed to `legalVector`.

This proof works for terminal pairs and when the exponent is bottom. Neither retention nor nonterminality is needed for this equality.

### SN13: actual nonterminal boundaries give the two crossings

From `hnt`, both boundary lengths differ from `K`. Applying `boundary_nonterminal` to `hp.1` and `hp.2.1` gives proper extensions of the ambient prefix and genuine crossings at `iy = y.length - 1` and `iz = z.length - 1`. `rawPair_prefix_join` and `hx.2` put each boundary before `x`; their strict positive extension lengths give

`A.w.length ≤ iy < (join y z).length ≤ x.length ≤ K`,

and the corresponding right inequality. Thus both witnesses lift to `Fin K` and lie in the exact required position set.

`leftIndex_mem` supplies a pile with probability at least `A.chi`, and `leftIndex_legal` supplies its `Fin k` bound. The genuine crossing puts that digit in the left-probability filter after prefix transport and SN2. All other summands are nonnegative, so the side sum is at least `A.chi`. The right argument is identical with the reversed inequality. This is exactly `TimeProfile.Crossings`.

No budget or additional finite-exponent premise is needed. The nonterminal premise is essential for this uniform conclusion because a terminal boundary can be a no-crossing fallback. `K=0` or an ambient word of length `K` makes these nonterminal premises impossible, which is correct. A genuine crossing at the last column is still terminal in the existing definition and is deliberately outside SN13.

### SN14: stop implies the numerical stability inequality

The existing `stop_iff_sub_lt hF` gives `Riffle.cL A x - F < A.delta`. SN4 at `u=x` rewrites the cost; strict-to-nonstrict implication gives precisely `TimeProfile.StableAt`. No boundary or ambient descent premise is needed for this implication between the literal definitions.

The equality `hF` is explicitly a premise identifying a real representative; it is not asserted for all pairs. In the eventual nonterminal application, `source_large_margin` returns such an `F` before its conditional `StableAt → ...` conclusion, so using SN14 at that point is not circular. Terminal and Lambda stable membership alone must not be substituted for `hstop`.

### SN15: the Gamma branch gives `ParentCrossing`

The projection `hx.1.1.1` is exactly `Riffle.Legal D x`: Gamma membership contains pair-descendant membership, which contains ambient-descendant membership, which contains legality. `gamma_first_crossing hp hroot hx` gives a strict join/word length inequality and non-Stop of the parent. The strict length inequality implies both `0 < x.length` and `(join y z).length ≤ x.length - 1`. `not_stop_iff_sub_ge hF`, followed by SN5, gives the final parent-cost inequality. These are exactly the three clauses of `TimeProfile.ParentCrossing`.

The root-not-stopped premise is retained and is necessary for the strict continuation conclusion. The nonterminal condition need not be added: in a terminal/root-not-stopped Gamma case the existing membership conditions would already be contradictory. No independent positivity or parent-legality assumption is missing.

### SN16: exact finite ambient approximation

Unfold `AmbientApproximation` and `logScale`. Apply SN8 with `u=A.w` and `hux=hx.2` to identify its prefix mass with the real expected count. The result is exactly the stated equivalence. It neither assumes the inequalities nor derives small errors from bare `Setup`.

The error parameters can be arbitrary reals in this equivalence. With a negative error both corresponding inequalities fail in the same way; no sign premise is needed for rewriting. `A.b` stays the original parameter, and no exact normalization is imposed. In particular the same right-hand side is valid for every continuation of the fixed ambient word.

## Proof-local facts and remaining boundaries

The implementation will need genuine finite reindexings and event identities, but no additional public theorem statement or hypothesis:

1. The value-map bijection between the two finite interval representations when the upper endpoint is at most `K`.
2. Coordinate agreement versus list prefix/take agreement for lists of known bounded length; actual sample legality is supplied by SN6.
3. The unique-full-vector decomposition of each row indicator, finite integral linearity, and coercion of NNReal finite sums/products.
4. Equality of the reindexed nonnegative suprema and the `toNNReal`/coercion identity.
5. Transfer of strict natural digit comparisons to `Fin` comparisons and the nonnegative-single-summand lower bound.
6. Proof irrelevance for legal-word proof parameters and positivity witnesses used by the profile adapter.

The candidate's dependency order is valid: D1–D4 and SN1–SN3; SN4–SN5; SN6–SN9; SN10–SN12; SN13 from boundary/probability facts; SN14–SN15 from cost/stopping facts; and SN16 from SN8. These match the earlier broad algebra report.

Actual stable membership still requires its existing branch split before invoking SN14 or SN15. Excluding Lambda uses the independently proved source terminal theorem with its actual analytic assumptions and error budget. The horizon relation, AlmostLike data, variational margin, ambient errors, and later profile-entropy normalization remain separate inputs or bridges; they are neither assumed silently nor proved by this finite contract. The stochastic endpoint density/localization obstruction also remains separate. None of these limitations invalidates an interface in SN1–SN16.
