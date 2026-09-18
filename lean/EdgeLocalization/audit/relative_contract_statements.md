# Proposed additive contract for ambient-relative edge coordinates

This independent pre-code statement report proposes exactly three definitions and eighteen theorems. It leaves all existing modules, mathematical sources, frozen statements, and prior reports unchanged. No implementation is authorized before independent comparison and a new freeze.

## 1. Source, interpretation, and scope

I reread the permitted TeX at 446–519, 1202–1258, 1486–1523, and 1640–1660. Lines 509–512 explicitly recenter ambient edge locations at the left endpoint of the ambient prefix interval. The internal edges themselves are defined by equal adjacent sorted rows at 460–467. The homogeneous PDF `2103.05068v3.pdf`, §4.1.1, gives `ι(w)=#{i:row_i<lex w}+1`, including empty cylinders; the fixed-column PDF `2510.22783v1.pdf`, (2.13)–(2.14), uses the same convention. I reread those endpoint definitions and the old translation arguments identified in the prior whole-file review.

All project deck positions are zero-based. Accordingly, the natural shift for the ambient prefix is `ι(w)-1`, namely the number of rows lexicographically below `w`. Relative left-edge position `i` denotes absolute left-edge position `i+shift`. This shifts a first occupied ambient vertex to relative vertex zero.

For a completely arbitrary nonnegative shift, the definition below can omit absolute edges lying before that shift. It is therefore initially a translated subgraph and has a cardinality inequality. Two additional deterministic theorems prove that the actual sorted-matrix ambient shift omits no internal child-block edge, and hence preserves its exact cardinality. This makes the ambient specialization a literal recentering of all source internal edges.

No identity between absolute and relative squared densities is asserted. The probability law remains the original full matrix law with population `N`. The same fixed support `range(N-1)` contains every possible relative edge coordinate; it can include unused coordinates beyond a realized ambient block. No random population or conditional law is substituted.

## 2. Definition inventory and argument conventions

All names are in namespace `EdgeLocalization`. `Relative` is a module directory, not another namespace. Numeric/deck arguments remain explicit. No new named instance, probability alias, cardinality alias, or ambient-density alias is proposed.

### R.D01 — `relativeInternalEdges`

Exact signature:

`(N : ℕ) (rows : ℕ → List ℕ) (xList : List ℕ) (s : ℕ) : Finset ℕ`.

Exact value:

`(Finset.range (N - 1)).filter (fun i => i + s ∈ internalEdges N rows xList)`.

Natural addition is used. The definition does not subtract from an absolute edge without first checking whether that edge lies after the shift.

### R.D02 — `relativeEdgeDensity`

Exact signature:

`{Ω : Type*} [Fintype Ω] (w : FiniteLaw Ω) (N : ℕ)`

`(R : Ω → ℕ → List ℕ) (xList : List ℕ) (shift : Ω → ℕ) : ℝ`.

Exact value:

`∑ i ∈ Finset.range (N - 1),`

`  (w.probability (fun ω => i ∈ relativeInternalEdges N (R ω) xList (shift ω))) ^ 2`.

`shift` can depend on the entire single outcome. It has no distributional, boundedness, independence, measurability, or positivity premise. Its values are nonnegative because its codomain is `ℕ`.

### R.D03 — `ambientLeft`

Exact signature:

`(N : ℕ) (rows : ℕ → List ℕ) (wList : List ℕ) : ℕ`.

Exact value:

`((Finset.range N).filter (fun i => rows i < wList)).card`.

The order is exactly the existing lexicographic `LinearOrder (List ℕ)` from `Mathlib.Data.List.Lex`, used by the already constructed sort. The comparison is strict, so rows extending `wList`, including rows equal to it at full length, are not counted. This definition is the zero-based insertion position even when the cylinder contains no row.

## 3. Complete deterministic theorem inventory

### R.01 — `relativeInternalEdges_subset_range`

Parameters:

`(N : ℕ) (rows : ℕ → List ℕ) (xList : List ℕ) (s : ℕ)`.

Conclusion:

`relativeInternalEdges N rows xList s ⊆ Finset.range (N - 1)`.

This is the literal filter support; no additional deck premise is required.

### R.02 — `relativeInternalEdges_zero_shift`

Parameters: `(N : ℕ) (rows : ℕ → List ℕ) (xList : List ℕ)`.

Conclusion: `relativeInternalEdges N rows xList 0 = internalEdges N rows xList`.

The existing `internalEdges_subset_range` supplies the reverse containment in the filtered equality.

### R.03 — `relativeInternalEdges_card_le`

Parameters are exactly R.01's parameters, in the same order.

Conclusion:

`(relativeInternalEdges N rows xList s).card ≤ (internalEdges N rows xList).card`.

The injection is `i ↦ i+s`; it is not a probability comparison at individual absolute/relative positions.

### R.04 — `ambientLeft_le_deck_size`

Parameters: `(N : ℕ) (rows : ℕ → List ℕ) (wList : List ℕ)`.

Conclusion: `ambientLeft N rows wList ≤ N`.

This follows from the filtered deck range. It is valid for arbitrary row maps, including unsorted ones.

### R.05 — `ambientLeft_nil`

Parameters: `(N : ℕ) (rows : ℕ → List ℕ)`.

Conclusion: `ambientLeft N rows [] = 0`.

The empty word is lexicographically minimal. This is the source's whole-deck zero-shift check.

### R.06 — `matrix_ambientLeft_le_internal_edge`

Parameters, in order:

`{N K k : ℕ} (n : Fin K → Fin k → ℕ) (ω : FixedMatrix N n)`

`(wList xList : List ℕ) (hprefix : wList <+: xList)`

`(i : ℕ) (hi : i ∈ internalEdges N (sortedRows n ω) xList)`.

Conclusion: `ambientLeft N (sortedRows n ω) wList ≤ i`.

The theorem uses the actual previously constructed sorted matrix rows. There is no `hn`, legality, word-length, assumed sorting, or assumed containment premise. An internal edge supplies prefix membership of its row; prefix transitivity implies `wList≤row_i` in lexicographic order. Every row below `wList` must have position below `i` by the proved sort monotonicity. Counting those positions proves the bound.

### R.07 — `matrix_relativeInternalEdges_card_eq`

Parameters, in order:

`{N K k : ℕ} (n : Fin K → Fin k → ℕ) (ω : FixedMatrix N n)`

`(wList xList : List ℕ) (hprefix : wList <+: xList)`.

Conclusion:

`(relativeInternalEdges N (sortedRows n ω) xList`

`  (ambientLeft N (sortedRows n ω) wList)).card =`

`(internalEdges N (sortedRows n ω) xList).card`.

R.06 makes subtraction of the ambient shift valid for every absolute edge. That inverse and the translation injection give a bijection. This proves equality of counts, not equality of edge sets with different coordinates or equality of their squared probability sums.

## 4. Generic probability theorems

The complete common parameter list for R.08, R.09, and R.11 is

`{Ω : Type*} [Fintype Ω] (w : FiniteLaw Ω) (N : ℕ)`

`(R : Ω → ℕ → List ℕ) (xList : List ℕ) (shift : Ω → ℕ)`.

The generic law may be nonuniform. Different edge positions within one outcome need not be independent.

### R.08 — `relative_density_le_sq_expected_absolute_edges`

Parameters: exactly the common generic list.

Conclusion:

`relativeEdgeDensity w N R xList shift ≤`

`(w.expectation (fun ω => (edgeCount N (R ω) xList : ℝ))) ^ 2`.

The expected edge count is the existing absolute edge count. R.03 bounds the expected relative count by it, and nonnegative squaring completes the generic density estimate.

### R.09 — `relative_density_le_expected_occupancy`

Parameters: exactly the common generic list.

Conclusion:

`relativeEdgeDensity w N R xList shift ≤`

`w.expectation (fun ω => (occupancyCount N (R ω) xList : ℝ))`.

Use probability-squared ≤ probability, the existing expected-cardinality identity, R.03, and the already proved absolute edge-count ≤ occupancy bound. No occupancy or shift estimate is a premise.

### R.10 — `relativeEdgeDensity_zero_shift`

Parameters:

`{Ω : Type*} [Fintype Ω] (w : FiniteLaw Ω) (N : ℕ)`

`(R : Ω → ℕ → List ℕ) (xList : List ℕ)`.

Conclusion:

`relativeEdgeDensity w N R xList (fun _ => 0) = edgeDensity w N R xList`.

This is the zero-shift specialization only. It does not equate the densities under a nonconstant shift.

### R.11 — `relativeEdgeDensity_eq_expected_shared_internal_edges`

Parameters: exactly the common generic list.

Conclusion:

`relativeEdgeDensity w N R xList shift =`

`(w.prod w).expectation (fun z =>`

`  ((relativeInternalEdges N (R z.1) xList (shift z.1) ∩`

`    relativeInternalEdges N (R z.2) xList (shift z.2)).card : ℝ))`.

Each independently sampled outcome uses its own value of the same shift function. The intersection compares the same relative coordinate in the two copies. The existing constructed `FiniteLaw.prod` supplies independence of the complete outcomes; no new product law or independence hypothesis is introduced.

## 5. Actual-matrix bounds for every shift

The exact parameter list for R.12–13 is

`{N K k M : ℕ} (n : Fin K → Fin k → ℕ)`

`(hn : ∀ j, ∑ a, n j a = N) (hM : M ≤ K) (x : Fin M → Fin k)`

`(shift : FixedMatrix N n → ℕ)`.

These statements retain all populations, empty alphabets/columns when the data exist, and zero piles. They impose no legality, lower-population, nonterminality, or small-mean premise.

### R.12 — `matrix_relative_density_le_mean_tail_fourth`

Conclusion:

`relativeEdgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x) shift ≤`

`(prefixMean N n hM x) ^ 4 * (tailCollisionFactor N n M) ^ 2 / 4`.

Apply R.08 and the already proved bound on the expected absolute internal-edge count, then square the nonnegative inequality. This must not be proved by assuming that relative density is at most absolute density; that comparison is not generally true.

### R.13 — `matrix_relative_density_le_prefixMean`

Conclusion:

`relativeEdgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x) shift ≤`

`prefixMean N n hM x`.

Apply R.09 and the existing exact expected sorted occupancy formula. The matrix law and every factor continue to use the original population `N`.

## 6. Ambient-left exponent specializations

For R.14–17 the exact common parameter list is the already frozen X.09–12 vector domain, unchanged:

`{N K k A M : ℕ} (n : Fin K → Fin k → ℕ)`

`(hn : ∀ j, ∑ a, n j a = N) (hM : M ≤ K) (hAM : A ≤ M)`

`(w : Fin A → Fin k) (x : Fin M → Fin k) (b : ℝ)`

`(hprefix : ∀ t, x (Fin.castLE hAM t) = w t)`

`(hN : 2 ≤ N) (hx : legalPrefix n hM x)`.

R.15–16 append their stated `δ` and cutoff. There is no explicit shift argument: the conclusions use the actual samplewise ambient-left shift.

The following are only display abbreviations, not new declarations:

- `Drel = relativeEdgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x)`
  `(fun ω => ambientLeft N (sortedRows n ω) (prefixWord w))`;
- `L = ambientSizeExponent N n hM A b x`;
- `ε = ambientMeanError N n (hAM.trans hM) w b`;
- `E = tailEdgeExponent N n M`.

### R.14 — `matrix_relative_density_le_ambient_tail_exponent`

Parameters: exactly the common ambient vector list.

Conclusion: `Drel ≤ Real.rpow (N : ℝ) (4 * (L + ε) + 2 * E) / 4`.

This is a consequence of R.12, the existing exact mean-power identity X.05, and the existing tail comparison X.08. Its scalar conversion is the one used in X.09, proved locally again for the new left-hand quantity; X.09's absolute density bound is not substituted for a relative-density bound.

### R.15 — `matrix_relative_density_le_small_coarse_exponent`

Parameters: the common ambient vector list, followed by

`(δ : ℝ) (hsmall : ambientSizeExponent N n hM A b x < 2 * δ)`.

Conclusion: `Drel ≤ Real.rpow (N : ℝ) (2 * E + 8 * δ + 4 * ε) / 4`.

### R.16 — `matrix_relative_density_le_small_singleton_exponent`

Parameters: exactly R.15's parameters, in the same order.

Conclusion: `Drel ≤ Real.rpow (N : ℝ) (2 * L + 2 * E + 4 * δ + 4 * ε) / 4`.

R.15 and R.16 keep arbitrary real `δ` with the displayed cutoff, not a cutoff on `L+ε`. They apply to every such legal prefix; no stable-family predicate or spatial gain is introduced. The signed error appears with coefficient four in both conclusions.

### R.17 — `matrix_relative_density_le_ambient_size_exponent`

Parameters: exactly the common ambient vector list, without a small-size hypothesis.

Conclusion: `Drel ≤ Real.rpow (N : ℝ) (L + ε)`.

Use R.13 and X.05.

### R.18 — `matrix_relative_density_terminal_exponent`

Parameters are exactly the frozen X.14 vector domain:

`{N K k A : ℕ} (n : Fin K → Fin k → ℕ)`

`(hn : ∀ j, ∑ a, n j a = N) (hA : A ≤ K)`

`(w : Fin A → Fin k) (x : Fin K → Fin k) (b : ℝ)`

`(hprefix : ∀ t, x (Fin.castLE hA t) = w t)`

`(hN : 2 ≤ N) (hx : legalPrefix n (Nat.le_refl K) x)`.

Conclusion:

`relativeEdgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x)`

`  (fun ω => ambientLeft N (sortedRows n ω) (prefixWord w)) ≤`

`Real.rpow (N : ℝ) (ambientSizeExponent N n (Nat.le_refl K) A b x +`

`  ambientMeanError N n hA w b)`.

This specializes R.17 at full length. The already proved X.13 supplies `tailEdgeExponent N n K=0`; it is not redefined or reproved as another new named theorem. There is no small-mean premise.

## 7. Proof dependencies and complete local auxiliary plan

No named declaration beyond the three definitions and eighteen theorems is proposed. In particular, no general shift-invariance theorem, assumed no-loss condition, generic prefix-order lemma, matrix sorting lemma, or new power-conversion helper is added.

1. **R.01–03:** the filter immediately supplies the support. For shift zero, addition reduces to the original index and existing edge support identifies the filter with the edge set. For arbitrary shift, membership supplies `i+s` in the absolute edge set and natural right-add cancellation proves injectivity. Apply the trusted finite-cardinality injection theorem.
2. **R.04–05:** filtered cardinality is bounded by the range cardinality. For the empty word, a local proof that no list is lexicographically below `[]` makes the filter empty. These do not assume rows are sorted.
3. **R.06:** the edge premise gives `i<N` and `xList <+: sortedRows n ω i`. Prefix transitivity gives `wList <+: sortedRows n ω i`. The required lexicographic inequality can be proved locally from a prefix-as-append witness: split its suffix into empty and nonempty cases, and use the trusted `List.Lex.append_left` in the nonempty case. For a counted position `j`, if `i≤j`, the previously proved `sortPermutation_monotone_rows` and the natural-index adapter give `row_i≤row_j`, contradicting `row_j<wList≤row_i`. Thus the counted set is contained in `range i`; compare cardinalities. Every row index used in sort monotonicity has its `Fin N` bound proved from the two memberships.
4. **R.07:** use the actual shift `s=ambientLeft...`. Translation `i↦i+s` maps every relative edge to an absolute edge. For each absolute edge `j`, R.06 gives `s≤j`, so `j-s+s=j`. Also `j-s≤j<N-1`, so the inverse is in the fixed relative support. These maps and natural cancellation prove a finite-set cardinal bijection, including empty edge sets. No global density identity is used.
5. **Vector interpretation of R.06–07:** when `wList=prefixWord w` and `xList=prefixWord x`, the common wrapper hypothesis `hprefix` proves `prefixWord w <+: prefixWord x`. This is a local application of the trusted list-prefix/get-element characterization, using the existing prefix-word length formula and the given coordinate equality. No separate public bridge or additional hypothesis is needed. The upper-bound wrappers use R.12–13 for arbitrary shifts, so they do not require this prefix-list conversion in their scalar proof; R.06–07 establish the complete source-recentering meaning independently.
6. **R.08:** apply the trusted nonnegative finite sum-of-squares bound to the relative membership probabilities. Existing `FiniteLaw.sum_probabilities_eq_expected_card` and R.01 identify their sum with the expected relative cardinality. Expectation monotonicity and R.03 bound this by the expected absolute edge count. Both expectations are nonnegative because their values are natural cardinalities, so their square comparison is justified locally.
7. **R.09:** the existing `sum_sq_probabilities_le_expected_card` and R.01 bound density by the expected relative count. Expectation monotonicity, R.03, and the existing `internalEdges_card_le_occupancy` give the conclusion.
8. **R.10–11:** the zero-shift theorem reduces through R.02 and the two density definitions. For independent copies, specialize the existing `FiniteLaw.expected_card_intersection` to the relative edge-set function and the support from R.01, then identify products of equal membership probabilities with squares. Each copy evaluates the shift at its own outcome. No independence between positions or between a graph and its own shift is used.
9. **R.12–13:** R.08 and the already proved `matrix_expected_internal_edges_le_half_mean_bound` give the fourth-power/tail-square bound after a nonnegative square comparison and real-ring normalization. R.09 and `matrix_expected_sorted_occupancy` give the mean bound. These arguments preserve the all-`N` domains of their existing finite inputs.
10. **R.14:** specialize R.12 to the actual ambient-left function. Use X.05 for the mean and X.08 with existing tail nonnegativity for the tail square. The trusted real-power multiplication/addition rules and ordinary real algebra give the exact exponent. All `N`/log/power conditions come from the unchanged `hN` and proved conversion lemmas.
11. **R.15–16:** specialize R.14 and compare exponents using respectively `4L≤8δ` and `4L≤2L+4δ`; positive-base power monotonicity follows from `N≥2`. Keep the denominator and signed ambient error unchanged.
12. **R.17–18:** R.13 plus X.05 gives the ambient mean exponent; specialize it to `M=K` for terminality. Any equality of length-bound proof terms uses proof irrelevance, not a hypothesis.

The main dependency chains are R.D01→R.01/R.03→R.08/R.09→R.12/R.13→R.14/R.17→R.15/R.16/R.18, and R.D03 plus existing sorting→R.06→R.07. R.11 uses R.01 and the existing overlap identity. The no-loss bridge and the arbitrary-shift bounds are logically independent until interpreting the actual ambient specialization.

Proposed module layout:

- `Relative/Model.lean`: exactly the three definitions;
- `Relative/Deck.lean`: R.01–07;
- `Relative/Density.lean`: R.08–13;
- `Relative/Estimates.lean`: R.14–18.

The deck module imports the existing sorted-row construction and lex order. The density module imports the existing finite intersection identity and collision estimates. The exponent wrappers import the existing exponent conversion. No existing module is edited.

## 8. Exhaustive domain and case audit

- **`N=0/1`:** `range(N-1)` is empty, so all relative edge sets and densities are zero. The deterministic, generic probability, and finite matrix theorems keep these cases. Exponent wrappers retain exactly the prior explicit `N≥2` domain. An edge membership premise in R.06 is impossible in these two cases; no invalid row index is constructed.
- **Shift zero:** R.02 and R.10 prove exact agreement with the existing absolute objects. R.05 supplies that shift for the empty ambient word.
- **Shift at least the deck size:** the relative set is empty by the absolute edge support. Generic inequalities remain valid; they do not pretend to preserve every absolute edge. The actual source shift has the additional no-loss theorem R.07.
- **Empty ambient cylinder:** `ambientLeft` remains its lexicographic insertion position. There are no internal child edges when the child extends that ambient, so R.07 has both sides zero. The shift may equal `N`; no first realized ambient row is required or chosen.
- **Empty ambient word, empty prefix, or `K=0`:** endpoint zero, empty-word prefixes, and empty matrix columns remain valid. With `K=0` all rows are equal empty words and the relative graph at the root is the same deterministic path as the absolute graph.
- **Empty alphabet or zero piles:** the same domains as the existing actual matrix model are retained. No alphabet inhabitance or positive pile count is introduced into the finite relative results. Exponent wrappers retain only the already frozen selected-prefix legality.
- **Arbitrary row maps:** R.01–05 and R.08–11 require no sorting or common row length. Their interpretation is the explicitly defined shifted subgraph. Only R.06–07 use actual `sortedRows`; its monotonicity is proved upstream rather than supplied as a new assumption.
- **Arbitrary sample dependence of the shift:** allowed. A shift may depend on every column and edge of its own matrix outcome. The two-copy identity draws independent complete outcomes; it does not assert the same joint distribution for shifts chosen by a function of both outcomes or a shared conditioning event.
- **Sorting ties and absent words:** the previous sort and lexicographic order handle ties. Prefix membership implies the needed weak lexicographic inequality even when a full row equals the ambient word. Strict `<wList` counts exactly rows before that cylinder.
- **Terminal prefixes:** R.18 needs no small-mean premise. Tail exponent zero is supplied by X.13. The same source signed ambient discrepancy is carried once.
- **Small prefixes and errors:** R.15–16 have the precise cutoff on `L`, arbitrary real `δ`, and coefficient `4ε`. Neither silently assumes the actual mean is small at a fixed `N` or removes a possibly nonzero signed error.
- **Null events and zero weight:** finite-sum identities and pointwise inclusions apply without division by probabilities. No nonempty event or positive-weight atom is needed.
- **Absolute versus relative overlap:** R.11 computes the overlap of the two recentered edge sets at matching relative positions. R.07 preserves each individual cardinality. Neither theorem identifies this overlap with overlap before the sample-dependent translations.

## 9. Independent design conclusion

This inventory proves numerical relative-density bounds directly from cardinalities, while separately certifying that the actual sorted ambient shift retains all source internal edges. It closes that deterministic coordinate-dependency gap without assuming a false density-translation identity or importing a spatial spread estimate. The same source error, full population, fixed count array, and exact probability law remain in every specialization.

No further named helper or assumption is needed for the displayed eighteen theorems. The draft is ready for the other independent agents' exact-statement comparison and the root's final freeze decision.

## 10. Statement-designer comparison and acceptance

After saving the complete inventory, I read `relative_contract_reconstruction.md` and `relative_contract_assumptions.md` in full. Their reconstruction and hidden-case audit agree with the exact three definitions and eighteen selected theorem statements above.

The reconstruction report also lists an immediate generic bound by the expected absolute edge count and optional matrix overlap-bound wrappers. Neither needs a separate declaration here: the former is a local step in R.09, and the latter follow by rewriting with the already selected R.11 and applying R.12 or R.13. This choice preserves the complete mathematical route while keeping the named inventory exactly R.D01–03 and R.01–18.

Both reports confirm the substantive source bridge. An arbitrary shift supports only the injective cardinality bound; the canonical ambient shift additionally satisfies the proved lower bound R.06 and exact cardinality equality R.07. Those two statements use actual sorted rows and an ordinary List-prefix relation, with no newly assumed sorting, containment, feasibility, or legality property. The source's vector prefix relation implies their List-prefix relation through the local get-element proof already described, without an additional public hypothesis or helper.

The comparison also confirms the one-based source offset is exactly the zero-based count `ι_w−1`, with a defined insertion cut for empty cylinders. The density support stays the fixed global `range(N−1)`, and both independently sampled copies use their own computed shift. All five exponent specializations retain exactly the earlier vector domains, original population, signed ambient discrepancy, numerical cutoffs, error coefficients, and constants.

The relative results do not identify independently recentered overlap with the global absolute-coordinate first moment. Any future aggregation or transfer between those quantities requires its own proved argument. Likewise, this addendum does not establish the printed negative-`c_F` spatial improvement, per-edge stable localization, concentration or endpoint windows, or singleton classification.

**Statement-designer acceptance:** no domain mismatch or additional named helper is needed. The candidate is complete and mathematically accepted with all displayed signatures unchanged, pending the reviewers' final exact-inventory confirmations and the root's freeze. No Lean implementation has been written, and all previous frozen modules and reports remain unchanged.
