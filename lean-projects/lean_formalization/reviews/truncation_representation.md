# Independent representation review of T01–T09

**Verdict: approve all nine candidate statements with the precise
representations below.** No additional mathematical assumption is
needed. The original F01–F20 and S01–S05 contracts remain unchanged.
No Lean code was written during this review, and dependency compilation
is a separate check by the coordinator.

Reviewed candidate SHA256:
`a6924e6543a135f596538080bb0f5e57b9a6e4ffeb15b9c55b7c4508292dea2b`.

I independently reread the relevant old arguments: the TeX definition
of boundary families and admissibility (lines 490–600), bad-profile
reduction (1039–1118), and the fixed-column convention; the 2025 PDF,
Section 2.2, Definition 4.3, Definition 4.7, and Lemmas 4.11–4.13; and
the 2021 PDF's Section 2 product-word construction and Section 4.1.1
prefix cylinders. Only the three authorized mathematical sources were
used. In particular, the 2021 model's independent rows must not be
carried over to the fixed-count model. The 2025 fixed-column construction
and the current project law have independent columns but dependent rows.

The present TeX and `Riffle.Admissible` use a non-strict admissibility
bound. The excluded event therefore has a strict real cutoff. The
older PDF's displayed strict admissibility convention is not substituted
for the current definition. Likewise, the proposed finite results do
not assert the source's subsequent small-parameter asymptotics.

## Exact existing interfaces

The inspected `Riffle` declarations are in
`formalization/stable_blocks/Riffle`:

- `Word` is `List ℕ`; `digit x i` uses `x[i]?.getD 0`.
- `Model` has fields `N`, `K`, `k`, `n : ℕ → ℕ → ℕ`,
  `one_lt_N : 1 < N`, `two_le_k : 2 ≤ k`, and
  `sum_counts : ∀ i, i < K → ∑ a ∈ Finset.range k, n i a = N`.
- `Legal D x` states `x.length ≤ D.K` and, at each in-range index,
  `digit x i < D.k` and `0 < D.n i (digit x i)`. `Full` adds
  `x.length = D.K`; `Cylinder D w` consists of legal full words having
  prefix `w`.
- `Setup D` has fields `w`, `w_legal`, `b`, `chi`, `chi_pos`,
  `chi_lt : chi < 1 / (D.k : ℝ)`, `C`, `C_pos`, `delta`, and
  `delta_pos`. These source fields are retained even when a particular
  truncation proof does not use `b` or `delta`.
- `prob D i a` is an `NNReal` ratio. `FullIndex D` is definitionally
  `Fin D.K → Fin D.k`. `fullList ω` is the `List.ofFn` of the natural
  digit values. `weight` is an `NNReal` finite product; `expectedCount`
  is `D.N` times a finite indicator-weight sum over `FullIndex D`.
- `Side` has constructors `.left` and `.right`. Left crossing means
  `leftIndex A i < digit`; a left violation means the reverse strict
  inequality. Right crossing and violation are reversed analogously.
- `violations A side x` counts violations in
  `Finset.Ico A.w.length x.length`, including the final digit.
  `Admissible` consists of `Boundary` membership plus the real upper
  bound on this natural count. `AdmissiblePair A y z` also contains
  `Compatible A y z`.

Useful proved interfaces are `Riffle.sum_prob`, `prob_le_one`,
`prob_lt_chi_of_lt_left`, `prob_lt_chi_of_right_lt`,
`leftIndex_legal`, `rightIndex_legal`, `digit_prefix`,
`fullList_length`, `fullList_digit`, `fullList_bounded`,
`fullList_injective`, `fullList_existsUnique`, `selected_spec`, and
`admissible_mem_boundary`. Importantly, `selected_spec` requires actual
membership in `Cylinder D A.w`; `fullList ω` is not assumed legal for
arbitrary `ω : FullIndex D`.

The relevant fixed-column interfaces are:

- `Shuffle.Histogram (Fin N) k` with fields `count : Fin k → ℕ` and
  `total : ∑ a, count a = Fintype.card (Fin N)`;
- `Shuffle.digitCount f a = Fintype.card {r // f r = a}`;
- `Shuffle.FixedColumn h = {f : Fin N → Fin k // ∀ a,
  digitCount f a = h.count a}`;
- existing finite and nonempty instances for `FixedColumn h`;
- `Shuffle.columnLaw h = Shuffle.FiniteLaw.uniform (FixedColumn h)`;
- `Shuffle.fixedMatrixLaw h`, a `FiniteLaw` on the dependent function
  type `∀ j, FixedColumn (h j)`, defined as the product of the column
  laws;
- `FiniteLaw.mass`, `mass_nonneg`, `mass_sum`, `prob`, `expect`, `map`,
  `uniform_prob`, `map_prob`, `map_expect`, `product_prob_rectangle`,
  and finite-sum expectation identities.

All sums, cardinalities, and probabilities below are over finite types.
Sets of `Word` need no measurability assumption because they occur only
as predicates pulled back to the finite word or matrix type.

## Shared new notation to freeze

These are names for literal adapters, not alterations of source objects:

1. `modelDigitProb D : Fin D.K → Fin D.k → ℝ` has value
   `(Riffle.prob D j.val a.val : ℝ)`.
2. `boundaryThreshold A : ℝ` is exactly
   `A.C / Real.log (1 / A.chi) * Real.log (D.N : ℝ)`.
3. `boundaryBadDigits A side j : Finset (Fin D.k)` filters `univ`
   by `a.val < leftIndex A j.val` for `.left`, and
   `rightIndex A j.val < a.val` for `.right`.
4. `discardedBoundary A side : Set Riffle.Word` is exactly
   `{x | x ∈ Cylinder D A.w ∧ selected A side x ∉ Admissible A side}`.
5. `modelColumnProfile D j : TimeProfile.Simplex D.k` has coordinates
   `modelDigitProb D j`, with no rounding or support deletion.

Use the existing `RiffleProfiles.wordWeight`, `badPositions`,
`badCount`, `badWordMass`, `tailWeight`, `lowCount`, `SparsePattern`,
and `BoundaryDescriptor` directly. Do not redefine their thresholds or
label conventions.

## T01 — approved

For arbitrary `D`, `j : Fin D.K`, and `a : Fin D.k`, the individual
contracts are nonnegativity of `modelDigitProb D j a`, normalization
`∑ a, modelDigitProb D j a = 1`, and the coordinate identity
`TimeProfile.prob (modelColumnProfile D j) a = modelDigitProb D j a`.
The two mass identities quantify over every `ω : FullIndex D` and
every `E : Set Word`, respectively:

`(weight D ω : ℝ) = wordWeight (modelDigitProb D) ω`,

`(expectedCount D E : ℝ) = (D.N : ℝ) *
  ∑ ω, if fullList ω ∈ E then wordWeight (modelDigitProb D) ω else 0`.

The existing natural-range normalization is transferred to `Fin D.k`
using `Fin.sum_univ_eq_sum_range`, then coerced from `NNReal` to real.
Nonnegativity is the `NNReal` coercion fact. Coercion commutes with the
finite product, sum, and indicator branches. These are exact identities
for arbitrary events and words, including words of zero product weight.
Construct the simplex subtype from these two coordinate facts; do not
introduce a probability-law premise.

## T02 — approved

Take `bad : Fin D.K → Finset (Fin D.k)`, `h : ℕ`, `a : ℝ`,
`ha : 0 ≤ a`, and
`hbad : ∀ j, ∑ d ∈ bad j, modelDigitProb D j d ≤ a`.
For arbitrary `E : Set Word`, retain exactly the pointwise inclusion
`∀ ω : FullIndex D, fullList ω ∈ E → h ≤ badCount bad ω`.
The conclusion is

`(expectedCount D E : ℝ) ≤
  (D.N : ℝ) * tailWeight D.K h a`.

First prove the indicator sum is bounded by `badWordMass` from event
inclusion and nonnegative word weights. Apply
`badWordMass_le_tailWeight` with T01's normalization, then multiply by
the nonnegative natural cast of `N`. The helper event-sum monotonicity
requires only nonnegative summands and the displayed inclusion. It does
not require `E` to consist of legal words or assume any sampling law.

## T03 — approved

`0 < boundaryThreshold A` follows from the existing source fields.
Since `D.k ≥ 2`, `A.chi < 1 / D.k ≤ 1`; together with `chi_pos`,
this gives `1 < 1 / A.chi` and hence a positive denominator logarithm.
`one_lt_N` gives positive `Real.log (D.N : ℝ)`, and `C_pos` supplies
the remaining positive factor. No separate `chi < 1` premise is added.

For every `j : Fin D.K` and `a ∈ boundaryBadDigits A side j`, prove
`modelDigitProb D j a < A.chi`. Case analysis on `side` invokes
`prob_lt_chi_of_lt_left` or `prob_lt_chi_of_right_lt` with the two
`Fin.isLt` bounds. This includes zero-size piles.

The main count conclusion, for every `ω : FullIndex D` satisfying
`fullList ω ∈ discardedBoundary A side`, is

`Nat.floor (boundaryThreshold A) + 1 ≤
  badCount (boundaryBadDigits A side) ω`.

Here and below `Nat.floor` means the natural floor of a real number,
not an integer floor followed by an unchecked cast. The proof must first
use the cylinder part of the discarded event to invoke `selected_spec`.
For `x = selected A side (fullList ω)`, this gives both boundary
membership and `x <+: fullList ω`. The remaining part of the event
then implies `boundaryThreshold A < (violations A side x : ℝ)` by the
literal `Admissible` definition.

Every violation index satisfies `A.w.length ≤ i < x.length ≤ D.K`.
`digit_prefix` and `fullList_digit` identify its digit with
`ω ⟨i, hiK⟩`. Thus the violation set embeds into the full-word
`badPositions`. A convenient finite proof compares the natural
violation set with the image of `badPositions` under `Fin.val`;
that image has unchanged cardinality because `Fin.val` is injective.
The strict real inequality and nonnegative threshold give the natural
`floor + 1` inequality, then cardinal monotonicity gives the conclusion.

This handles terminal fallback through `selected_spec` itself. If the
ambient prefix is already terminal, the selected extension is empty,
its violation count is zero, and the discarded premise is impossible
because the threshold is positive. No terminal exclusion is inserted.

## T04 — approved

Apply T02 with
`h = Nat.floor (boundaryThreshold A) + 1` and
`a = (D.k : ℝ) * A.chi`. T03 supplies the event inclusion and a
strict per-digit smallness bound; weaken that bound to `≤` only as a
derived fact for F18. Summing at most `D.k` such digits gives the
required coordinate bound. Positivity of `chi` supplies `a ≥ 0`.

The one-side conclusion is exactly

`(expectedCount D (discardedBoundary A side) : ℝ) ≤
  (D.N : ℝ) * tailWeight D.K (Nat.floor (boundaryThreshold A) + 1)
    ((D.k : ℝ) * A.chi)`.

For the union, use the same `expectedCount` applied to
`discardedBoundary A .left ∪ discardedBoundary A .right`. Pointwise
indicator subadditivity yields at most the sum of the one-side bounds,
equivalently twice the displayed bound. Disjointness is not assumed.
No high-tail unweighted count or asymptotic exponent is involved.

## T05 — approved; relative coordinates must be explicit

Let `m = x.length - A.w.length` and
`h = Nat.floor (boundaryThreshold A)`. Define an encoding on
`{x : Word // x ∈ Admissible A side}` into the unchanged
`BoundaryDescriptor D.K h D.k` as follows:

- The length component is `m : Fin (D.K + 1)`. Its bound follows from
  `A.w <+: x` and `Legal D x`.
- If `m = 0`, the final-digit component is the fixed `0 : Fin D.k`,
  available from `D.two_le_k`. If `m > 0`, it is
  `digit x (x.length - 1)`, bounded by legality.
- The sparse position set is the set of **relative** indices
  `t : Fin D.K` such that `t.val + 1 < m` and the digit at absolute
  index `A.w.length + t.val` is a violation for the specified side.
  At each such position store that digit as an element of `Fin D.k`.

The descriptor's exact constraint is `t.val + 1 < m`, not `t.val < m`:
its labelled deviations are strictly before the final digit. The labels
form the dependent function on the chosen finite set demanded by
`SparsePattern`; do not extend them to unconstrained full-word labels.

The sparse set has cardinality at most `violations A side x`, by the
injective shift `t ↦ A.w.length + t.val`. The admissibility inequality
gives `violations A side x ≤ Nat.floor (boundaryThreshold A)`, so the
sparse cardinal bound is proved from the input subtype. Excluding the
last violation, if present at terminal fallback, is harmless because
that last digit is stored separately.

The required reconstruction helper is: in any `Boundary A side`, at
each index `A.w.length ≤ i < x.length - 1`, there is no crossing.
This follows from either branch of the literal `BoundaryCut` definition,
including terminal fallback. If that index is also not a violation,
the digit equals `leftIndex A i` or `rightIndex A i`, respectively.
Thus equal descriptors give equal lengths and equal digits by three
cases: the fixed ambient prefix, a pre-final extension digit (stored
violation or forced extreme), and the separately stored final digit.
When `m = 0`, both words equal the fixed ambient prefix directly.
List extensionality proves injectivity. No full-word extension or
unused suffix is part of this code.

The exact finite conclusions can be stated as separate finiteness and
natural-cardinality theorems, avoiding a `Fintype` prerequisite on the
infinite ambient list type:

`Finite {x : Word // x ∈ Admissible A side}`,

`Nat.card {x : Word // x ∈ Admissible A side} ≤ B`,

where the natural number
`B = D.k * (D.K + 1) * lowCount D.K h D.k`.

Obtain finiteness from the injection into the finite descriptor type,
then use `boundaryDescriptor_card_le` and `D.two_le_k` for the bound.
For pairs the domain is
`{yz : Word × Word // AdmissiblePair A yz.1 yz.2}`.
Its injection into the product of the two admissible boundary subtypes
gives finiteness and cardinality at most `B ^ 2`. The source
`Compatible` field is retained in the pair subtype; it can only restrict
the image. These statements do not count all natural-number lists.

## T06 — approved

Use `p : Fin K → TimeProfile.Simplex k`, `P : BorelPartition k`,
arbitrary real `C`, and exactly the premises
`P.IsRegular chi C`, `0 < chi`, `2 ≤ N`, `0 ≤ alpha`.
Take `v M : (Fin K → Fin k) → ℕ` with no additional conditions.
Let `L = TimeProfile.logScale N` and define

`bad j = Finset.univ.filter (fun a => ¬P.IsGoodDigit chi (p j) a)`.

For a full word `ω`, its exceptional prefix set is the filter of
`TimeProfile.positions K (v ω) (M ω)` by `ω j ∈ bad j`. This is
definitionally the exceptional predicate in the candidate. Let
`pReal j a = TimeProfile.prob (p j) a`.

The unambiguous mass conclusion is

`∑ ω, (if alpha < (E ω).card / L then wordWeight pReal ω else 0)
  ≤ tailWeight K (Nat.floor (alpha * L) + 1) ((k : ℝ) * (3 * chi))`,

where the cardinality is cast to real before division. Its `N`-scaled
version multiplies both sides by `(N : ℝ)`.

The pointwise helper is `E ω ⊆ badPositions bad ω`; no endpoint
ordering is needed to prove it. From `L > 0`, the strict event implies
`alpha * L < (E ω).card`, and since `alpha * L ≥ 0` its natural
integer threshold is `Nat.floor (alpha * L) + 1`. Combine this with
cardinality monotonicity to obtain the full-word event inclusion.

For every `a ∈ bad j`, source regularity gives
`TimeProfile.prob (p j) a ≤ 3 * chi` through
`BorelPartition.IsRegular.exceptional_actual_le`. Coordinate
nonnegativity and normalization are source simplex facts. Apply the
existing F18 small-digit union-tail theorem with threshold `3 * chi`.
This proves the finite mass bound even when the endpoints depend
arbitrarily on the complete word. It does not require legality, positive
mass at every digit, `v ω ≤ M ω`, or either endpoint to be at most `K`.
The existing finite position filter handles clipped and empty intervals.

## T07 — approved

For `h : Shuffle.Histogram (Fin N) k`, retain `hN : 0 < N` and
quantify over `r : Fin N` and `a : Fin k`. The exact target is

`(Shuffle.columnLaw h).prob (fun f => f.val r = a)
  = (h.count a : ℝ) / (N : ℝ)`.

The pre-approved proof should include the following finite helpers:

1. For `e : Equiv.Perm (Fin N)`, precomposition `f ↦ f ∘ e`
   preserves every `digitCount`. This follows from the explicit
   equivalence of digit fibres induced by `e`.
2. Consequently, precomposition defines an equivalence of
   `FixedColumn h` with itself; the inverse uses `e.symm`.
3. Uniform probability is invariant under this equivalence. An exact
   law formulation is `(columnLaw h).map permuteColumn = columnLaw h`;
   equivalently its probability of `E ∘ permuteColumn` equals its
   probability of any event `E`. This follows from uniform finite
   counting and the equivalence, not an assumed symmetry axiom.
4. Taking a transposition of rows gives equal probabilities
   `P(f r = a) = P(f s = a)` for any `r,s`.
5. The sum over rows of the indicator of digit `a` equals `h.count a`
   in every outcome. Finite summation of probabilities therefore gives
   `(N : ℝ) * P(f r = a) = (h.count a : ℝ)`.

Divide only after using `hN`. A prescribed digit count of zero is
allowed; the same equality gives marginal zero. The `FixedColumn`
nonempty instance comes from the feasible histogram's existing `total`
field, not from an added positive-count assumption.

## T08 — approved

Define `modelHistogram D j : Shuffle.Histogram (Fin D.N) D.k` with
`count a = D.n j.val a.val`. Its `total` proof is precisely
`D.sum_counts j.val j.isLt`, rewritten from a natural range to
`Fin D.k` and using `Fintype.card_fin`.

Use `Shuffle.fixedMatrixLaw (modelHistogram D)` unchanged. The outcome
type is the dependent function type
`∀ j : Fin D.K, Shuffle.FixedColumn (modelHistogram D j)`.
For an outcome `matrix` and `r : Fin D.N`, define
`rowWord matrix r : Riffle.FullIndex D` by
`rowWord matrix r j = (matrix j).val r`.

The first exact contract quantifies over each row and full index:

`(Shuffle.fixedMatrixLaw (modelHistogram D)).prob
  (fun matrix => rowWord matrix r = ω)
  = wordWeight (modelDigitProb D) ω`.

Function extensionality identifies this event with the rectangular
event `∀ j, (matrix j).val r = ω j`. The proved
`FiniteLaw.product_prob_rectangle` and T07 give the product of the
ratios `D.n j (ω j) / D.N`, which is exactly the T01 word weight.
This is column independence already encoded in the constructed law.
Zero counts cause zero factors without any exceptional case premise.

For every `E : Set Riffle.Word`, the expected-cardinality contract is

`(Shuffle.fixedMatrixLaw (modelHistogram D)).expect
  (fun matrix => (((Finset.univ.filter (fun r : Fin D.N =>
    Riffle.fullList (rowWord matrix r) ∈ E)).card : ℕ) : ℝ))
  = (Riffle.expectedCount D E : ℝ)`.

A natural cardinality cannot be passed to `expect` without the real
cast. Convert it to the finite sum of indicators, exchange the finite
row and outcome sums, then use each row's proved word marginal. Every
row contributes the same indicator sum over full indices. Summing over
`Fin D.N` gives the factor `D.N`, and T01 identifies the right side.
The intermediate event-to-word sum can also be expressed by the
`FiniteLaw.map` of `rowWord`; its atom masses are exactly the proved
word weights.

No claim of independence between rows occurs. Arbitrary events may
contain impossible or illegal words: their corresponding word weights
vanish as a consequence of the marginal identity, with no legality
premise attached to `E`. When `K = 0`, the product law and full-index
type each have one empty-coordinate outcome, and these identities still
hold.

## T09 — approved

The two boundary corollaries specialize T08 to the exact discarded
event and its left/right union and apply T04. Their expected row counts
are bounded by `D.N * tailWeight` and twice that same expression,
respectively, with precisely the T04 threshold and small-mass parameter.

For the exceptional-prefix corollary use `p = modelColumnProfile D`,
`N = D.N`, and retain the T06 data `P`, `chi`, `C`, `alpha`, `v`, `M`
and its premises. `2 ≤ D.N` follows from `D.one_lt_N`. The exact bound
is

`(D.N : ℝ) * tailWeight D.K
  (Nat.floor (alpha * TimeProfile.logScale D.N) + 1)
  ((D.k : ℝ) * (3 * chi))`.

There is a small representation bridge to make explicit: T06's event
is a predicate `Q` on `FullIndex D`, whereas T08 accepts `Set Word`.
Take `E = Riffle.fullList '' {ω : FullIndex D | Q ω}`. The existing
`fullList_injective` proves
`fullList ω ∈ E ↔ Q ω` for every full index. Thus T08's row count and
word-mass sum become exactly the corresponding T06 expressions. This
does not extend the endpoints to arbitrary lists, introduce arbitrary
suffixes, or weaken the event. An equivalent generic finite-row-event
corollary of T08 is also legitimate if this same pullback equality is
proved first.

The corollaries concern actual expected row counts under the explicit
matrix law. Sorting rows, identifying a graph edge set, squared edge
probabilities, ordered limits, or negative powers of `N` are not part of
these conclusions.

## Dependency order and final review conditions

The finite proof dependencies are

`T01 → T02`, `T03 + T02 → T04`,
`source Boundary + T03 threshold facts + F19 → T05`,
`source regularity + F18 → T06`,
`finite uniform symmetry → T07`, `T01 + T07 → T08`, and
`T04 + T06 + T08 → T09`.

All elementary helpers described above have been reviewed here before
implementation: real/NNReal coercion, finite event monotonicity, threshold
positivity and natural-floor conversion, prefix violation inclusion,
relative sparse encoding and reconstruction, fixed-column permutation
invariance, row-marginal double counting, rectangular full-word events,
finite expected-cardinality sums, and the `fullList` image pullback.
Their assumptions are derived from or identical to their parent
contracts. No unreviewed analytic bridge is needed by this batch.

Before freezing, spell out the real casts in tail parameters and row
cardinalities, the natural floor convention, T05's relative-coordinate
encoding and finite-subtype cardinality formulation, and T09's exact
event pullback. These are representation clarifications of the
candidate, not requests for new hypotheses. No change to F/S assumptions
or mathematical definitions is approved or necessary.
