# Independent adversarial review of T01–T09

**Decision: approve every candidate statement, with no added hypotheses or
changes to the mathematical conclusions.** The implementation obligations
below specify the existing domains and conventions; they do not authorize
modifying F01–F20, S01–S05, the source definitions, or the sampling law.

Reviewed candidate SHA-256:
`a6924e6543a135f596538080bb0f5e57b9a6e4ffeb15b9c55b7c4508292dea2b`.

## Sources and interfaces checked

Re-read the current TeX definitions of the two boundary families and
admissibility (lines 534–599), retained terminal pairs (645–659), source
exceptional positions (699–741), and the old bad-profile argument
(1040–1118). Also re-read 2510.22783v1, Section 2.2 and Definition 4.3,
Definition 4.7, and Lemmas 4.11–4.12, together with 2103.05068v3,
Sections 4.1.1–4.1.3. Only those authorized mathematical sources and current
Lean interfaces were used.

The finite source model is `formalization/stable_blocks/Riffle`:
`Definitions.lean` defines `Model`, `Setup`, `FullIndex`, `expectedCount`,
the boundary cut, and the actual admissibility test. `Model.lean` proves
normalization and smallness outside the extreme large piles.
`Boundary.lean` proves the selected-prefix specification, including
terminal fallback. `Words.lean` proves prefix digit equality and the
full-index/list conversion. The actual probability law is in
`lean/Shuffle/FixedColumns.lean`, built from the proved finite-law machinery
in `FiniteLaw.lean` and `Conditioning.lean`.

## Individual decisions

### T01 — approved

`prob` is the nonnegative ratio of natural column counts to `D.N`
(`Riffle/Definitions.lean:53`). `Model.lean:36` proves its column sum is one;
`Fin.sum_univ_eq_sum_range` transfers it to `Fin D.k`. Coercing the product
in `weight` and the finite sum in `expectedCount` gives exactly the proposed
identities (`Definitions.lean:56–65`). The normalized real coordinate
function therefore belongs to `TimeProfile.Simplex`, whose defining
conditions are nonnegativity and sum one (`RiffleTimeProfile/Base.lean:20`).

No legality premise is required on a full index. A selected zero-count
digit makes its word weight zero; `Mass.lean:16` already proves this for
illegal full words. Arbitrary sets of natural-number lists are harmless:
the functional sums only over `fullList` images. When `K=0`, the sole
full index is the empty function, its weight is one, and the functional is
`N` times the indicator that the empty list belongs to the set.

### T02 — approved

The stated event inclusion and nonnegative word weights give a pointwise
indicator domination. Summing it, applying
`RiffleProfiles.badWordMass_le_tailWeight`, and multiplying by `D.N ≥ 0`
proves the bound. Its coordinate hypotheses are exactly those in frozen
F18 and are supplied by T01 and the stated bound on each bad-set mass.
The inclusion must remain quantified over every full index, as written.
There is no stochastic-independence premise at this stage.

`h=0`, empty bad sets, `a=0`, and `h>K` are covered by the finite formula.
In particular the last case forces the dominated event to be empty on
full indices and `tailWeight K h a = 0`.

### T03 — approved

`Setup` supplies `0 < χ < 1/k`, `C>0`, and `Model` supplies `N>1`, `k≥2`.
Thus `χ<1`, both logarithms in `tau` are positive, and `tau>0`.
`Model.lean:93` and `:105` prove the strict per-digit bound `< χ` for the
left and right bad sets; their index hypotheses follow from the `Fin`
domains. Zero piles cause no exception.

For a discarded full word, `selected_spec` (`Boundary.lean:141`) first
proves that its selected prefix is a boundary. Consequently failure of
`Admissible` means **strictly** `tau < violations`. For a natural count
`q` and nonnegative real `tau`, this is equivalent to
`Nat.floor tau + 1 ≤ q`, including when `tau` is an integer. The selected
prefix's violation positions inject into the full set of bad positions:
their indices are below the selected length, hence below `K`, and
`digit_prefix` and `fullList_digit` identify their labels.

Terminal fallback has the same violation count and inclusion. If the
ambient prefix is already terminal, selection returns that prefix and its
extension violation set is empty; the discarded event is empty. This also
covers `K=0` and the empty ambient word. No first-crossing existence premise
may be added to this theorem.

### T04 — approved

Apply T02–T03 with threshold `floor(tau)+1`. The sum of masses of bad digits
is at most `k*χ`: strict smallness implies the weak per-digit estimate
needed by F18, and there are at most `k` digits. The union estimate is a
finite union bound, with the same factor `N` on both sides. Disjointness of
the two discarded events is unnecessary and generally false.

There is no exemption for an inadmissible terminal boundary. The paper's
statement that retained terminal pairs are kept follows its restriction
to admissible boundary families (TeX:595 and 645); the existing Lean global
coverage also requires both admissibility tests (`Riffle/Global.lean:15–32`).
Thus the candidate's definition of `discarded` is the correct one. An
admissible terminal pair is not discarded merely for being terminal.

### T05 — approved

Write `m=|w|`, `L=|x|-m`. A boundary lies in `Desc D w`, so `m≤|x|≤K` and
`0≤L≤K`. Encode the extension length `L`, its final digit when `L>0`
(digit zero otherwise), and the labelled pre-final violations at
**relative positions** `i-m`. For these positions, `i+1<|x|`, hence their
encoded position satisfies `j+1<L`, exactly as required by
`BoundaryDescriptor` (`RiffleProfiles/Counting.lean:143–146`).

The encoded violation count is at most the actual violation count, hence
at most `floor(tau)` by admissibility. A final fallback digit may itself be
a violation; it is stored separately, so deleting it from the sparse
pattern neither loses information nor exceeds the count budget.

Injectivity follows by recovering all list digits. The ambient portion is
fixed; labelled violations are stored; every remaining pre-final digit is
forced to equal the appropriate extreme index because it is neither a
crossing nor a violation. Both alternatives of `BoundaryCut` give the
needed absence of earlier crossings (`Definitions.lean:92–96`). The final
digit is explicitly stored. An empty extension yields the unique ambient
word. Natural subtraction is used only after `m≤|x|` is established.

The resulting injection proves finiteness of the actual admissible list
subtype and its bound by `B`. The admissible-pair subtype injects into the
product of the two admissible boundary subtypes; compatibility can only
reduce its cardinality, giving `B²`.

Do not replace this subtype by full-index realizations of the boundary.
A prefix of length `M` generally has `k^(K-M)` full extensions, which would
invalidate this counting argument. Also do not omit the final label:
with `K=1`, `w=[]`, `k=2`, masses `(3/4,1/4)`, and `χ=3/10`, the left
boundaries `[0]` and `[1]` have the same extension length and empty
pre-final violation pattern. Their final digits distinguish them.

### T06 — approved

The displayed set is exactly `TimeProfile.exceptionalPositions`
(`Digits.lean:21–23`), with normalization `profileR` (`:50–52`). Set
`bad j={a | ¬P.IsGoodDigit χ (p j) a}`. For every full word, the exceptional
set is a subset of its full bad-position set, regardless of how `v` and
`M` depend on the word. Thus no stopping-time, endpoint-independence, or
order premise is needed.

Since `N≥2`, `L=logScale N>0`; the strict event becomes
`alpha*L < card(E)`. Since `alpha≥0`, its natural threshold is exactly
`floor(alpha*L)+1`. Source regularity gives each bad digit mass at most
`3*χ` (`Base.lean:187–190`). Its coordinate bad mass is therefore at most
`k*(3*χ)`, and F18 gives precisely the candidate tail. Multiplication by
`N` preserves the inequality. Empty/clipped intervals, zero actual or
representative coordinates, `alpha=0`, `K=0`, and thresholds above `K`
are all included. In particular no union over possible endpoints is
needed. Nonnegativity of `alpha` is already correctly present: without
it, an empty exceptional set could satisfy the event while the proposed
positive-threshold tail is zero.

### T07 — approved

`FixedColumn h` fixes every histogram count, and `columnLaw h` is the
uniform law on that finite nonempty type (`FixedColumns.lean:22–66`).
Precomposing a column with a row permutation preserves each digit count
by a bijection of its row fibre. The inverse permutation makes this an
equivalence of column outcomes. Constant uniform outcome mass therefore
proves invariance; it must not be inserted as a hypothesis.

A permutation exchanging any two rows proves equality of their digit
marginals. For every column outcome the sum of the row indicators of
digit `a` equals `h.count a`. Finite summation and normalization then give
`N*q=h.count a`, and division by `N>0` gives the claimed marginal. This
argument divides only by `N`, never by `h.count a`, and works when the
digit's count is zero. No independent-row assertion is involved.

### T08 — approved

`D.sum_counts` constructs the histogram at each column without any
existence assumption. `fixedMatrixLaw` is explicitly the product of the
uniform column laws (`FixedColumns.lean:283–286`). The event that a fixed
row is a specified full word is a coordinate rectangle, so
`FiniteLaw.product_prob_rectangle` (`Conditioning.lean:561`) and T07 give
its product mass. This applies to the **unsorted labelled matrix rows**.

For an arbitrary word-set `E`, finite summation over the row-word fibres
gives the row event probability; summing these probabilities over rows
gives the expected cardinality by linearity. T01 identifies the result
with `expectedCount`. No row independence is needed, and no prefix is
counted repeatedly: this step deliberately ranges over complete
`FullIndex` values. Zero-probability illegal words and `K=0` behave as
described under T01.

Two distinctions must survive implementation. For `N=2`, `K=1`, counts
`(1,1)`, the rows are dependent: both being zero has probability zero,
not `1/4`. Moreover, the first **sorted** row is always zero, so the
product marginal formula is false for that sorted position. Counts of
rows in a fixed word-set are permutation invariant, but a bridge through
sorting must prove that fact rather than reusing the marginal formula at
a sorted row index.

### T09 — approved

T08 substitutes the actual expected cardinality into T04, both for each
side and for their union. For T06, a full-word event can be represented
as a set of natural-number words using the image under `fullList`.
`fullList_injective` (`Words.lean:151`) proves the inverse membership
equivalence required to apply T08. The endpoints may still be arbitrary
functions of the full index. No prefix-invariance assumption is needed
to transport an event on complete words.

The exceptional expected-count bound retains the factor `N`; dropping it
would confuse product probability with expected row count, as in the
source sketch's display at TeX:1101. These conclusions are the stated
finite expected-row bounds. They do not by themselves prove an assertion
about a sorted shuffle-graph edge set, a variance, or any ordered limit.

## Boundaries of this approval

The weighted high-tail bound used here is valid. The source sketch's
unweighted enumeration of all high-exception patterns remains false and
is not used. T05 is a boundary count, not the unresolved estimate on the
size of a coarse profile class: storing only exceptional positions still
does not fix exceptional digit costs. The previously reported
time-measurability obstruction and the analytic/asymptotic obligations
also remain. No new Lean code or frozen-file modification was made during
this review.
