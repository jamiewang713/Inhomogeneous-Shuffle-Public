# Independent reconstruction of T01–T09

## Verdict

Approve all nine finite candidate statements in `TRUNCATION_CANDIDATE.md` without changing their assumptions or conclusions. No additional support, endpoint order, row independence, time measurability, stochastic marginal, or asymptotic premise is needed. The exact proof routes are given below. This is a pre-implementation mathematical/interface review; no Lean code was written for this batch.

The mathematical sources used are only the authorized current TeX and the two authorized PDFs. The actual boundary interfaces were read from `formalization/stable_blocks/Riffle`, which is now authoritative. The fixed-column probability interfaces are in `lean/Shuffle/FiniteLaw.lean`, `lean/Shuffle/Conditioning.lean`, and `lean/Shuffle/FixedColumns.lean`. A scan of those interfaces and the relevant stable-block definition, model, word, boundary, and mass modules found no `axiom`, `sorry`, `admit`, or `opaque` declaration. I have not independently recompiled those dependencies during this review; their recorded source proof bodies must still be checked by the implementation toolchain.

There is one source-scope qualification, not a correction to the candidate. The actual `Riffle.Admissible` definition applies the violation threshold to terminal boundary words as well as crossing words. Thus `discarded` includes a terminal fallback if it violates that threshold. The current TeX says both that admissibility truncates the displayed complete boundary families (lines 582–598) and, later, that terminal retained pairs are not included in the discard (lines 1091–1093). T03–T05 correctly follow the actual definitions and do not establish that blanket exemption sentence. Empty ambient extensions have zero violations and are not discarded because the threshold is positive.

## Independent rereading of the source proofs

The current TeX, lines 447–457, defines legal words and uniform fixed-count columns; lines 2917–2923 explicitly state independence of the columns. Its admissible families, lines 582–598, use the number of digits on the wrong side of the extreme large pile, including the terminal coordinate in the counting interval. The proof of `lem:ub-bad-profile-reduction`, lines 1051–1120, reduces discarded contributions to expected row mass, then gives the weighted binomial tails and the small-profile counting argument.

In 2510.22783v1, Definition 4.3 (PDF page 18) gives the first-crossing boundaries. Lemma 4.11 (PDF page 26) counts sparse boundary descriptions; Lemma 4.12 (pages 26–27) exploits the small coordinate probabilities of excluded boundaries. The proof of Proposition 4.2 (pages 32–33) truncates many exceptional digits and groups by labelled exceptional data. These arguments support the mechanisms in T03–T06, but the new finite proof should retain actual digit labels and an explicit stopping/final-digit record. The source's informal count of a fixed set of locations is not by itself an injection.

In 2103.05068v3, the construction on PDF pages 5–6 generates independent rows of independent digits; equations (4.1)–(4.3) on PDF page 16 give binomial prefix and endpoint distributions in that model. That row-independence argument must not be imported into T07–T09. The current fixed-column model has dependent rows. Exchangeability within a column, independence between columns, and linearity of expectation suffice for the candidate statements.

The current TeX's unweighted count of all exceptional patterns above a small threshold (lines 1103–1105) is not used: that high-tail count can be exponentially large. T02, T04, and T06 instead use the already proved weighted F18 tail. T09 keeps the factor `N` for expected row cardinality. No small-power or ordered-limit claim is inferred at this stage.

## Common existing interfaces

The stable-block declarations have the following exact roles:

* `Riffle.Model` (`Definitions.lean:20`) supplies `1 < N`, `2 ≤ k`, and the integer column sums on valid columns. `Riffle.Setup` (`Definitions.lean:41`) supplies the fixed legal ambient prefix and the existing positive constants with `0 < chi < 1/k`.
* `Riffle.prob`, `FullIndex`, `fullList`, `weight`, and `expectedCount` (`Definitions.lean:53`–65) are respectively NNReal coordinate ratios, full finite-index words, natural-number lists, product weight, and `N` times a weighted indicator sum.
* `Riffle.sum_prob`, `prob_le_one`, and the two small-pile lemmas `prob_lt_chi_of_lt_left` / `prob_lt_chi_of_right_lt` are proved in `Model.lean`.
* `Riffle.fullList_length`, `fullList_digit`, `fullList_injective`, and `digit_prefix` are proved in `Words.lean`. `fullList` is injective on the entire finite-index word type, including zero-weight illegal words.
* `Riffle.selected_spec` (`Boundary.lean:141`) proves that the selected prefix is a boundary prefix of the original full legal word. `boundary_mem_desc` supplies its legality and ambient prefix relation. The `BoundaryCut` definition itself records absence of every earlier crossing, including in the terminal-fallback branch.
* `RiffleProfiles.badWordMass_le_tailWeight`, `badWordMass_smallDigits_le_tailWeight`, and `scaled_badWordMass_le_tailWeight` are the proved F18 weighted bounds. `boundaryDescriptor_card_le` is the proved F19 descriptor bound.

The bundled Model/Setup fields remain source hypotheses; no adapter should claim to prove them. Conversely, a permutation-invariance or row-marginal conclusion is not a field of `Shuffle.Histogram` or of `columnLaw`: those are new proof obligations explicitly included in T07.

## T01 — normalized columns and the finite product functional

Fix `j : Fin D.K` and `a : Fin D.k`. The real coordinate is the NNReal coercion of `Riffle.prob D j.val a.val`.

1. Nonnegativity follows from the NNReal coercion. Convert `Riffle.sum_prob D j.val j.isLt` from the sum over `Finset.range D.k` to the sum over `Fin D.k`, then coerce to Real. This gives the exact total 1, with no omitted zero-count coordinates.
2. Coerce the finite product defining `Riffle.weight` into Real. Coercion commutes with multiplication and finite products, so the result is exactly `RiffleProfiles.wordWeight p_D omega`.
3. Unfold `expectedCount`. Coercion commutes with the natural scalar, finite sum, and the two branches of the indicator. Replacing each weight by step 2 gives the displayed identity for every set of natural-number words. No legality of members of that set is assumed.
4. Package the real coordinate function and the proved nonnegativity/normalization into `TimeProfile.Simplex D.k`. This constructs `modelColumnProfile` with coordinate equality by definition; it does not assert any regular partition or time law for those points.

The dependence is purely definitional plus `Riffle.sum_prob`. The provided model has `N > 1`; division normalization is therefore legitimate even when a selected count is zero.

## T02 — event inclusion into the weighted tail

After T01, divide no new quantity: write the actual `expectedCount` as `N` times its finite indicator sum. For every full index `omega`, prove

`(if fullList omega ∈ E then wordWeight p_D omega else 0) ≤ (if h ≤ badCount bad omega then wordWeight p_D omega else 0)`.

If the event holds, use the stated event implication. If it does not hold, use nonnegativity of the product weight. Summing this pointwise inequality bounds the event sum by `badWordMass p_D bad h`. Apply F18's `badWordMass_le_tailWeight`, using T01 normalization and nonnegativity and precisely the candidate's `a ≥ 0` and bad-coordinate-mass bounds. Multiply by the nonnegative real cast of `D.N`.

The event implication is the only event-specific premise. It remains valid for illegal full-index words and words of weight zero. Column independence is not a new premise here: `wordWeight` is already the defined product functional; its connection to the actual matrix law is deferred to T08.

## T03 — actual selected boundaries force the global bad-count event

First, `D.two_le_k` and `A.chi_lt` imply `A.chi < 1`; together with `A.chi_pos`, this gives `1 < 1/A.chi` and hence `Real.log (1/A.chi) > 0`. `D.one_lt_N` gives `Real.log D.N > 0`. Therefore `tau(A) > 0` from `A.C_pos`.

For each valid column and digit, membership in the left bad set is exactly `a.val < leftIndex A j.val`; membership in the right bad set is exactly `rightIndex A j.val < a.val`. The existing small-pile lemmas give the strict bound `< A.chi`, using the `Fin` bounds for their required valid-column and alphabet premises.

Now take `omega` with `fullList omega ∈ discarded(A,s)` and put `y = selected A s (fullList omega)`. Membership in the ambient cylinder permits `selected_spec`, giving both `y ∈ Boundary A s` and `y <+: fullList omega`. Since `y` fails `Admissible` but is a boundary, the remaining conjunct of the admissibility definition fails:

`tau(A) < (violations A s y : Real)`.

Convert this strict real inequality to `floor(tau(A)) + 1 ≤ violations A s y`; positivity of `tau` supplies the nonnegative-domain fact needed by the natural-floor equivalence.

Inject the actual violation set into the full bad-position set. A violation position `i` satisfies `|w| ≤ i < |y| ≤ D.K`. Map it to the corresponding element of `Fin D.K`. The map is injective by equality of natural values. `digit_prefix` identifies `digit y i` with `digit (fullList omega) i`, and `fullList_digit` identifies the latter with `(omega ⟨i, hiK⟩).val`. Thus the mapped selected digit belongs to `bad(A,s,i)`. Cardinality monotonicity gives

`violations A s y ≤ badCount (bad(A,s)) omega`.

Composing proves the exact floor-plus-one conclusion. The proof never assumes a genuine crossing: it applies equally to terminal fallback. If the extension is empty, the violation count is zero, contradicting strict exclusion because `tau > 0`; no special exemption premise is required.

## T04 — boundary expected-mass truncation

For either side, strict smallness from T03 implies the non-strict per-digit bound needed by F18. Summing over at most `D.k` digits gives coordinate bad mass at most `(D.k : Real) * A.chi`. This quantity is nonnegative. Apply T02 with the actual discarded event and `h = floor(tau(A)) + 1`, using T03's event implication. The result is exactly the displayed one-side bound.

For two sides, prove `expectedCount(D,E ∪ F) ≤ expectedCount(D,E) + expectedCount(D,F)` by the pointwise indicator inequality and nonnegative weights, then apply the two equal tail bounds. This is an upper bound for a union, not a disjointness assertion. The common tail is finite even if the threshold exceeds `D.K`, in which case the event inclusion forces an empty event on positive-weight words and the frozen tail is zero.

## T05 — injection of actual boundary prefixes

Let `d = A.w.length`, and for an actual admissible boundary `x` let `m = x.length - d`. Ambient-prefix legality gives `d ≤ x.length ≤ D.K`, so `m ≤ D.K` and `d + m = x.length`.

Construct the descriptor as follows:

1. The stopping field is `m : Fin (D.K+1)`, the relative extension length.
2. If `m = 0`, use digit zero in `Fin D.k`; this is available from `D.two_le_k`. If `m > 0`, use the actual final digit `digit x (x.length-1)`, with its bound `< D.k` from legality. This field is required for terminal fallback too.
3. Let the sparse support be the relative positions `r : Fin D.K` satisfying `r.val + 1 < m` and a violation at absolute coordinate `d + r.val`. Label every such relative position with the actual digit there. The support condition is exactly the frozen descriptor's strict pre-final condition.
4. Map this support injectively into the actual violation set by `r ↦ d + r.val`. Its image lies in the interval defining `violations`, so its cardinality is at most `violations A s x`. Admissibility gives `(violations : Real) ≤ tau`; the natural-floor equivalence yields `violations ≤ floor(tau)`. Hence the support is a valid frozen `SparsePattern`.

For injectivity, descriptors with equal stopping field give equal total lengths because the ambient length is fixed. Compare the digits of two encoded words:

* At indices below `d`, both words equal the fixed ambient prefix.
* At the final extension index, the final-digit fields agree.
* At a pre-final extension index in the sparse support, its label gives the digit.
* At every other pre-final extension index, the boundary definition supplies absence of a crossing and absence from the support supplies absence of a violation. For the left side these are respectively `digit ≤ leftIndex` and `leftIndex ≤ digit`; for the right side they are `rightIndex ≤ digit` and `digit ≤ rightIndex`. The digit is therefore forced to be the appropriate extreme index.

The needed absence-of-crossing fact holds in both disjuncts of `BoundaryCut`: in the crossing branch it is stated for every index before the final digit; in the fallback branch it is stated through `D.K-1`, which includes every pre-final index. Thus a terminal final violation is safely encoded by the final-digit field even though it is absent from the sparse pre-final support. The empty-extension case gives `x = A.w` directly from the prefix relation and equal lengths.

This reconstructs every actual admissible word uniquely, proving an injection into the existing finite descriptor type. Derive finiteness of the admissible subtype from that injection before using its cardinality; do not assume finiteness of an unrestricted natural-list type. Frozen `boundaryDescriptor_card_le` with `D.two_le_k` then gives the candidate `B`. Finally map an `AdmissiblePair` to its two admissible boundary subtype elements. This map is injective; compatibility only restricts the domain. The product count gives the upper bound `B^2` without a separate compatibility or suffix-count factor.

## T06 — exceptional prefixes with word-dependent endpoints

Define the global bad-digit set at a column by

`bad(j) = {a : Fin k | not P.IsGoodDigit chi (p j) a}`.

This family depends only on the fixed column profile and partition, not on the selected word. Source regularity gives `prob (p j) a ≤ 3*chi` for every bad digit; `3*chi > 0`. Simplex membership gives coordinate nonnegativity and total 1, so F18 bounds the full-word bad-count event with parameter `(k : Real) * (3*chi)`.

For each individual `omega`, its specified exceptional-prefix set is a subset of `badPositions bad omega`, regardless of how the two endpoints depend on that word. This is immediate from its defining filtered `positions` membership. Therefore its cardinality is at most `badCount bad omega`.

`N ≥ 2` gives positive `L = logScale N`. From `alpha < card(E(omega))/L`, multiply by `L` to obtain `alpha*L < card(E(omega))`. Since `alpha ≥ 0`, the threshold is nonnegative, and the natural-floor equivalence gives `floor(alpha*L)+1 ≤ card(E(omega)) ≤ badCount bad omega`. The same pointwise nonnegative-indicator comparison as T02 bounds the product mass of the exceptional-prefix event by the full-word F18 tail, exactly as displayed in T06.

No legality is needed: impossible digits contribute zero weight and no logarithm of a selected probability is used. No order or bound on the endpoint functions is needed: `positions` clips to `Fin K`, and reversed/empty intervals simply have no positions. Multiplication by the natural scalar `N` preserves the inequality. No asymptotic value of `alpha` is selected here.

## T07 — deriving the actual uniform-column marginal

`Shuffle.Histogram` (`FixedColumns.lean:22`) prescribes counts summing to the number of rows. `FixedColumn` is the subtype of all assignments realizing those counts. `fixedColumn_nonempty` (`FixedColumns.lean:48`) proves feasibility, including zero-count digits. `columnLaw` (`FixedColumns.lean:65`) is the literal uniform `FiniteLaw` on this finite nonempty subtype.

For every row permutation `e : Equiv.Perm (Fin N)`, precomposition `f ↦ f ∘ e` preserves each digit count. Prove this using the equivalence of digit fibres induced by `e`. Precomposition and precomposition by `e.symm` then give an equivalence of the whole fixed-column outcome type. Uniform probability is invariant under this equivalence: either reindex the constant-mass finite sum, or use `FiniteLaw.uniform_prob` (`Conditioning.lean:345`) and equality of the corresponding event-fibre cardinalities. This proves invariance for every event, rather than assuming exchangeability as a marginal formula.

Apply invariance to the swap of any two rows. Their probabilities of digit `a` are equal. Write their common marginal as `q_a`, and calculate

`N*q_a = sum_r P(f(r)=a) = E(sum_r 1_{f(r)=a}) = E(h.count a) = h.count a`.

The middle identity follows by exchanging two finite sums. For every outcome the indicator sum equals `digitCount f a`, and the subtype property makes that equal to the prescribed count. `FiniteLaw.mass_sum` or `expect_const` gives the last equality. Since the candidate explicitly assumes `N > 0`, division by `N` yields `q_a = (h.count a : Real)/N`.

If `h.count a = 0`, the same calculation yields marginal zero. Neither digit positivity nor independence between different row coordinates is assumed or needed. This proof uses no factorial cardinality formula for fixed columns.

## T08 — full row marginal and actual expected count

For each valid `j`, construct `h_j : Shuffle.Histogram (Fin D.N) D.k` with `h_j.count a = D.n j.val a.val`. Its total is the existing model total after converting the natural-range sum to the `Fin` sum. No feasibility premise is added; `fixedColumn_nonempty` handles it.

The experiment type is the dependent product of these fixed-column types. Its law is the existing `Shuffle.fixedMatrixLaw` (`FixedColumns.lean:284`), definitionally `FiniteLaw.product (fun j => columnLaw h_j)`. A fixed row's word is `rowWord matrix r = fun j => (matrix j).val r`.

For a fixed row `r` and full word `omega`, equality `rowWord matrix r = omega` is equivalent, by function extensionality, to the coordinate rectangle `forall j, (matrix j).val r = omega j`. Apply the existing `FiniteLaw.product_prob_rectangle` (`Conditioning.lean:561`). Apply T07 to each coordinate. NNReal-to-Real division compatibility identifies the resulting product with `wordWeight p_D omega` exactly. No relation between the words of two different rows has been used.

For an arbitrary set `E` of natural words, expand the row cardinality as a sum of real indicator values. Swap the finite matrix/row sums in its expectation. For each fixed row, partition the experiment by its full row-word value; the resulting sum is

`sum_omega (if fullList omega ∈ E then wordWeight p_D omega else 0)`.

This equality can be proved by a second finite-sum interchange and the unique value of the function `rowWord`, or by the already proved finite pushforward definitions. It is identical for every row, so summing over `Fin D.N` contributes exactly `D.N`. T01 then identifies it with `coe(expectedCount D E)`.

The domain remains the actual product of fixed-histogram columns. The statement is not a conditional expectation and not an independent-row replacement model. Sets containing words of the wrong length or illegal words are harmless: both sides only evaluate them through actual full-index words, with impossible words having zero marginal mass.

## T09 — actual expected row truncations

For a boundary side or their union, take exactly the natural-word discarded event in T08 and substitute the expected-count bounds from T04. This immediately gives the one-side or twice-one-side finite tail for the actual expected number of discarded rows.

For exceptional-prefix truncation, use `modelColumnProfile D` from T01 and the given regularity data for the specified partition. The exceptional event is naturally a predicate on `FullIndex D`, whereas T08 is stated for natural-word sets. Define its natural-word set as the image under `fullList` of those full indices satisfying the predicate. `Riffle.fullList_injective` proves that pullback of this set along `fullList` is exactly the original exceptional event, even when the endpoint functions depend on the complete word. T08 and the multiplied T06 bound then give exactly

`expected exceptional row count ≤ D.N * tailWeight D.K (floor(alpha*logScale D.N)+1) (D.k*(3*chi))`.

All regularity and alpha premises here are precisely those already present in T06, instantiated with the model profile; none is silently supplied by Model. The result counts rows once by their specified exceptional event. It is not a bound for a sum that counts the same row repeatedly over arbitrary prefix families.

The sorted-graph edge comparison, treatment of mixed retained/discarded shared edges, any decision to exempt terminal pairs, and all ordered-limit estimates remain separate subsequent obligations as the candidate states.

## Dependency order for this batch

`T01 → T02`; `T01 + existing boundary/word lemmas → T03`; `T02 + T03 → T04`; `existing boundary definitions + F19 → T05`; `F18 + source regularity → T06`; `uniform-column definitions → T07`; `T01 + T07 + existing product law → T08`; `T04 + T06 + T08 → T09`.

T05 and T06 can therefore be established independently of the actual matrix marginal proof. None of T01–T09 depends on an integral/time-law bridge or changes frozen F01–F20 or S01–S05.
