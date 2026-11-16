# Proposed additive collision contract: statement design

This is an independently designed proposal for comparison before an additive freeze. It does not alter `frozen_contract.md`, its definitions D1–D8, its statements F01–F33, or any manuscript statement. No Lean implementation is authorized by this document alone.

The mathematical source is the permitted TeX: the uniform fixed-column matrix law and lexicographic sorting at lines 388–392 and 446–454; internal block counts and ambient recentering at 490–518; the internal-edge uses at 1553–1556 and 1572–1575; and the small-singleton and terminal targets at 1507–1511 and 1640–1659. The exact finite estimates below supply a previously unimplemented matrix-law obligation. They do not prove the printed spatial factor involving `c_F`, a stable-profile estimate, or the conditional exploration assertions at 1923–1943.

## 1. Model choice and quantifier discipline

Use the uniform distribution directly on the finite subtype of columns with prescribed counts. A product of these laws is exactly the source's independent uniform fixed-column model. Uniform permutations of a canonical pile list would give the same law, but would introduce an unnecessary pushforward-uniformity proof. Row permutations are needed only to prove exchangeability of the direct uniform law and to describe sorting.

The top-level deterministic data are:

- `N K k : ℕ`;
- `n : Fin K → Fin k → ℕ`;
- `hn : ∀ j : Fin K, ∑ a : Fin k, n j a = N`.

There is no assumption that `N`, `K`, `k`, or an individual pile count is positive. There is no almost-like condition, stable-block condition, concentration assumption, independence field, moment field, or probability-bound field. Count nonnegativity follows from the type `ℕ`; the displayed sum condition is the prescribed-column-size condition from the source.

A prefix is represented by:

- `M : ℕ`;
- `hM : M ≤ K`;
- `x : Fin M → Fin k`.

Its existing-deck representation is the list `prefixWord x : List ℕ` of digit values in increasing coordinate order. This permits zero-count digits. Thus the finite results hold for every alphabet word of permitted length, including every legal word in the manuscript. Positivity of its selected counts is needed only by subsequent logarithmic exponent definitions and is not added here.

All probabilities and expectations in this proposal are unconditioned under the explicit finite matrix law. In particular, the ambient prefix `w` is not a conditioning event or a change from population `N` to `|B_w|`. For any deterministic `w` that prefixes `x`, the full-prefix formula already applies to `x`; no further ambient hypothesis is needed for these full-deck coordinate counts. Relative-coordinate densities and conditional residual laws require separate statements if they are later implemented.

All equality between probability laws below means equality of `FiniteLaw` values, or, where stated explicitly, equality of their weight functions. No equality-in-law fact is a constructor field.

## 2. Proposed definitions and finite instances

These are mathematical definitions with their intended Lean types. The syntax in this report specifies types and formulas; it is not a Lean implementation.

**C.D01 — `FiniteLaw.uniform`.** For `Ω : Type u`, `[Fintype Ω]`, `[Nonempty Ω]`, define a `FiniteLaw Ω` with weight

`uniform.weight ω = (Fintype.card Ω : ℝ)⁻¹`.

Nonnegativity and normalization are proved in the constructor from positive finite cardinality. The `Nonempty` instance is only the necessary domain condition for a uniform probability law; for each fixed-column space it is derived from `hn` by C.06 below.

**C.D02 — `FiniteLaw.pi`.** For `ι : Type u`, `[Fintype ι]`, `Ω : ι → Type v`, `[∀ j, Fintype (Ω j)]`, and `w : ∀ j, FiniteLaw (Ω j)`, define a law on `∀ j, Ω j` with weight

`(pi w).weight ω = ∏ j, (w j).weight (ω j)`.

The normalization proof uses the finite product-of-sums identity. The empty index type gives weight one on its unique function. No `Nonempty (Ω j)` assumption is required by this constructor beyond the given normalized laws.

**C.D03 — `FixedColumn`.** For `N k : ℕ` and `n : Fin k → ℕ`, define

`FixedColumn N k n = {c : Fin N → Fin k // ∀ a, (Finset.univ.filter (fun i => c i = a)).card = n a}`.

Provide a `Fintype` instance derived from the finite function type and its subtype. No field of this subtype expresses a probability.

**C.D04 — `FixedColumn.reindex`.** For `π : Equiv.Perm (Fin N)`, define an equivalence of `FixedColumn N k n` with itself by

`(reindex π c).val i = c.val (π i)`.

The count-preservation proof is C.08; the inverse uses `π.symm`. The equivalence is a definition justified by proved histogram invariance, not an assumed action.

**C.D05 — `columnLaw`.** Given `h : ∑ a, n a = N`, define `columnLaw n h : FiniteLaw (FixedColumn N k n)` as C.D01, using the derived inhabitance C.06. Its weights do not depend on the proof term `h`.

**C.D06 — `FixedMatrix` and `matrixLaw`.**

`FixedMatrix N K k n = ∀ j : Fin K, FixedColumn N k (n j)`.

Its `Fintype` instance is derived from the dependent function space. Define `matrixLaw n hn` as `FiniteLaw.pi (fun j => columnLaw (n j) (hn j))`.

**C.D07 — `prefixWord`.**

For `x : Fin M → Fin k`, `prefixWord x = List.ofFn (fun t => (x t).val)`.

**C.D08 — `rawRow` and `rowsOfLabels`.**

For `ω : FixedMatrix N K k n` and `i : Fin N`,

`rawRow ω i = List.ofFn (fun j : Fin K => ((ω j).val i).val)`.

For any `R : Fin N → List ℕ`, define `rowsOfLabels R : ℕ → List ℕ` by `rowsOfLabels R i = R ⟨i,hi⟩` when `hi : i < N`, and `[]` otherwise. Proof irrelevance makes this independent of the bound proof. Define `rawRows ω = rowsOfLabels (rawRow ω)`.

This is only an adapter to frozen D2–D5; those definitions remain unchanged.

**C.D09 — `sortedLabels`.** For `R : Fin N → List ℕ`, take `List.finRange N` and apply `List.mergeSort` using the comparison `R i ≤ R j`, where `List ℕ` has its lexicographic linear order. In the Boolean merge-sort API the comparison is `decide (R i ≤ R j)`.

The elements being sorted are the distinct original row labels. Equal row words may occur, but they do not create duplicate labels. The relation on labels need only be total and transitive; it need not be antisymmetric.

**C.D10 — `sortPermutation`.** For `R : Fin N → List ℕ`, define a permutation of `Fin N` whose forward map sends a position `i` to the `i`th element of `sortedLabels R`. Cast `Fin N` to `Fin (sortedLabels R).length` using C.24's proved length equality, and compose with the trusted `List.Nodup.getEquivOfForallMemList`, whose domain is the index type and whose codomain is the label type. Its arguments are C.26's proved absence of duplicates and occurrence of every label. No sortedness, inverse, or reindexing fact is assumed in this definition.

**C.D11 — `sortedRows`.**

`sortedRows ω = rowsOfLabels (fun i => rawRow ω (sortPermutation (rawRow ω) i))`.

These are the source's sorted words, in zero-based positions. The default outside `[0,N)` is `[]`, as for raw rows. All count and edge operations are the existing frozen definitions.

**C.D12 — one-column factors.** For `n : Fin k → ℕ` define real quantities

`singleFactor N n a = (n a : ℝ) / (N : ℝ)`;

`pairFactor N n a b =`

- `((n a * (n a - 1) : ℕ) : ℝ) / ((N : ℝ) * ((N - 1 : ℕ) : ℝ))` if `a = b`;
- `((n a * n b : ℕ) : ℝ) / ((N : ℝ) * ((N - 1 : ℕ) : ℝ))` if `a ≠ b`.

`coincidenceFactor N n = ∑ a : Fin k, pairFactor N n a a`.

All subtraction inside the natural numerators and `N - 1` is truncated natural subtraction before casting. Thus the formulas remain total when a pile is zero or `N ≤ 1`. For `N ≤ 1`, the pair factors are algebraic zero values; there are no distinct row labels to which a two-row probability theorem would apply.

**C.D13 — prefix and tail factors.** The bound proof `hM` supplies the inclusion `ι : Fin M → Fin K` with `ι(t).val=t.val`.

`prefixMass n hM x = ∏ t : Fin M, singleFactor N (n (ι t)) (x t)`;

`prefixPairFactor n hM x = ∏ t : Fin M, pairFactor N (n (ι t)) (x t) (x t)`;

`tailCollisionFactor n M = ∏ j ∈ Finset.univ.filter (fun j : Fin K => M ≤ j.val), coincidenceFactor N (n j)`;

`tailSquareFactor n M = ∏ j ∈ Finset.univ.filter (fun j : Fin K => M ≤ j.val), ∑ a : Fin k, (singleFactor N (n j) a)^2`.

The empty products are one. `tailCollisionFactor` and `tailSquareFactor` do not need a length-bound proof in their definitions.

**C.D14 — `prefixMean`.**

`prefixMean n hM x = (N : ℝ) * prefixMass n hM x`.

This is an explicit expression whose equality to expected occupancy is proved, not a field or an assumption.

## 3. Complete proposed named lemma inventory

The list below is the complete planned project-level theorem inventory for this proposal. Constructor proof terms and ordinary local `have` statements may prove intermediate equalities within these statements. They do not authorize additional named assumptions or unproved declarations. Trusted mathlib results can be used directly without adding wrappers merely to rename them.

For every matrix statement, the leading parameters are exactly `N K k n hn` from section 1; for every prefix statement they are followed by `M hM x`. No theorem about the actual matrix law adds probabilistic hypotheses. Any additional parameters or assumptions are stated in its entry.

### Finite-law foundations

**C.01 — `FiniteLaw.uniform_probability`.** For every finite nonempty `Ω` and `A : Ω → Prop`,

`uniform.probability A = ((Finset.univ.filter A).card : ℝ) / (Fintype.card Ω : ℝ)`.

Predicates and equalities use local classical decidability, matching the existing finite-law file.

**C.02 — `FiniteLaw.uniform_probability_reindex`.** For every finite nonempty `Ω`, `e : Ω ≃ Ω`, and `A : Ω → Prop`,

`uniform.probability (fun ω => A (e ω)) = uniform.probability A`.

**C.03 — `FiniteLaw.pi_probability`.** For the exact parameters of C.D02 and events `A : ∀ j, Ω j → Prop`,

`(pi w).probability (fun ω => ∀ j, A j (ω j)) = ∏ j, (w j).probability (A j)`.

**C.04 — `FiniteLaw.pi_probability_on_finset`.** For the same parameters, a finset `s : Finset ι`, and the same event family,

`(pi w).probability (fun ω => ∀ j ∈ s, A j (ω j)) = ∏ j ∈ s, (w j).probability (A j)`.

This follows from C.03 by using the true event off `s`; it handles empty prefix and tail events without a positivity requirement on the number of columns.

**C.05 — `FiniteLaw.probability_disjoint_indexed_union`.** For arbitrary existing `w : FiniteLaw Ω`, a finite type `α`, and `A : α → Ω → Prop`, assume exactly `∀ ω a b, A a ω → A b ω → a = b`. Then

`w.probability (fun ω => ∃ a, A a ω) = ∑ a, w.probability (A a)`.

This is a generic finite partition identity, not a shuffle-law assumption. In its column use disjointness follows from the uniqueness of the digit of a row.

### Prescribed columns and exact probabilities

**C.06 — `fixedColumn_nonempty`.** For every `N k n` and `h : ∑ a, n a = N`, `Nonempty (FixedColumn N k n)`.

Construct a column from an equivalence `Fin N ≃ Σ a : Fin k, Fin (n a)`, obtained by the equality of finite cardinalities. The fiber of the projection to `a` has exactly `n a` points. This includes the empty sigma type when `N=0`; no canonical nonempty digit is required.

**C.07 — `pile_count_le_total`.** For the same deterministic data and every `a : Fin k`, `n a ≤ N`.

**C.08 — `column_count_reindex`.** For all `c : Fin N → Fin k`, `π : Equiv.Perm (Fin N)`, and `a : Fin k`,

`(univ.filter (fun i => c (π i) = a)).card = (univ.filter (fun i => c i = a)).card`.

**C.09 — `ordered_distinct_pair_card`.** For every `N`,

`((univ ×ˢ univ : Finset (Fin N × Fin N)).filter (fun p => p.1 ≠ p.2)).card = N * (N - 1)`.

**C.10 — `column_ordered_fiber_pair_card`.** For every `c : FixedColumn N k n` and `a b : Fin k`, the cardinality of

`(univ ×ˢ univ).filter (fun p => p.1 ≠ p.2 ∧ c.val p.1 = a ∧ c.val p.2 = b)`

is `n a * (n a - 1)` when `a=b`, and `n a * n b` when `a≠b`. The equality case and distinct-digit case are proved separately.

**C.11 — `exists_perm_map_pair`.** For any `N`, `i j i' j' : Fin N`, `hij : i ≠ j`, and `hij' : i' ≠ j'`, there is `π : Equiv.Perm (Fin N)` with `π i = i'` and `π j = j'`.

The hypotheses express precisely the two distinct labels being mapped. They imply `N≥2`; no probability is involved. Use a trusted permutation-extension theorem directly if available, otherwise prove this finite statement by swaps with all overlapping-label cases.

**C.12 — `column_probability_reindex`.** For `N k n h`, `π : Equiv.Perm (Fin N)`, and any event `A` on `FixedColumn N k n`,

`(columnLaw n h).probability (fun c => A (FixedColumn.reindex π c)) = (columnLaw n h).probability A`.

**C.13 — `column_one_probability`.** For `N k n h`, every `i : Fin N` and `a : Fin k`,

`(columnLaw n h).probability (fun c => c.val i = a) = singleFactor N n a`.

The proof uses exchangeability in `i` and the deterministic identity that exactly `n a` labels have digit `a`. An index `i : Fin N` already implies `N>0`; there is no missing `N=0` event.

**C.14 — `column_two_probability`.** For `N k n h`, `i j : Fin N`, `hij : i ≠ j`, and `a b : Fin k`,

`(columnLaw n h).probability (fun c => c.val i = a ∧ c.val j = b) = pairFactor N n a b`.

Use C.11–C.12 to obtain the same probability for every ordered distinct label pair. Sum those probabilities using existing F12, C.09 and C.10. Prove `N≥2` from `hij` before dividing. The cases `a=b` and `a≠b` remain explicit.

**C.15 — `column_equal_probability`.** For `N k n h`, `i j : Fin N`, and `hij : i ≠ j`,

`(columnLaw n h).probability (fun c => c.val i = c.val j) = coincidenceFactor N n`.

Apply C.05 to the disjoint alternatives `c i = a ∧ c j = a` and C.14.

**C.16 — `column_zero_count`.** For any `c : FixedColumn N k n`, `a : Fin k`, and `ha : n a = 0`, every `i : Fin N` satisfies `c.val i ≠ a`.

**C.17 — `matrixLaw_uniform_weight`.** For every `ω : FixedMatrix N K k n`,

`(matrixLaw n hn).weight ω = (Fintype.card (FixedMatrix N K k n) : ℝ)⁻¹`.

This identifies the product law with uniform sampling among all matrices with the given counts, as stated at TeX lines 388–389. Inhabitance is derived coordinatewise from C.06, and product cardinality proves the weight formula.

### Prefix and row adapters

**C.18 — `prefixWord_length`.** For every `x : Fin M → Fin k`, `(prefixWord x).length = M`.

**C.19 — `rawRow_length`.** For every `ω` and `i : Fin N`, `(rawRow ω i).length = K`.

**C.20a — `rowsOfLabels_apply`.** For every `R : Fin N → List ℕ` and `i : Fin N`, `rowsOfLabels R i.val = R i`.

**C.20b — `rowsOfLabels_outside`.** For every `R : Fin N → List ℕ`, `t : ℕ`, and `ht : N ≤ t`, `rowsOfLabels R t = []`.

**C.21 — `prefixWord_prefix_rawRow_iff`.** For every matrix sample `ω` and `i : Fin N`,

`prefixWord x <+: rawRow ω i ↔ ∀ t : Fin M, (ω (ι t)).val i = x t`.

**C.22 — `rawRow_eq_iff`.** For every `ω` and `i j : Fin N`,

`rawRow ω i = rawRow ω j ↔ ∀ t : Fin K, (ω t).val i = (ω t).val j`.

**C.23 — `prefixWord_represents_list`.** For every `xList : List ℕ` such that `∀ a ∈ xList, a < k`, there exists `x : Fin xList.length → Fin k` with `prefixWord x = xList`.

This is the bridge showing the vector-prefix theorems cover every source word, rather than changing the prefix convention. Its construction uses the actual entries of `xList`; it makes no positivity claim about pile counts.

### Sorting and frozen count invariance

**C.24 — `sortedLabels_length`.** For every `R : Fin N → List ℕ`, `(sortedLabels R).length = N`.

**C.25 — `sortedLabels_perm`.** For every such `R`, `List.Perm (sortedLabels R) (List.finRange N)`.

**C.26 — `sortedLabels_nodup_mem`.** For every `R : Fin N → List ℕ`, `(sortedLabels R).Nodup ∧ ∀ i : Fin N, i ∈ sortedLabels R`.

C.25 transfers both facts from `List.finRange N`. The trusted `List.Nodup.getEquivOfForallMemList` then gives the needed index-to-label equivalence directly in C.D10. No project theorem about duplicate-word matching or generic indexing bijectivity is needed.

**C.27 — `sortPermutation_monotone_rows`.** For every such `R` and `i j : Fin N` with `i ≤ j`,

`R (sortPermutation R i) ≤ R (sortPermutation R j)`.

The relation on row words is lexicographic. This certifies that the actual row adapter C.D11 is a sorted source deck. The total/transitive key relation permits `List.sorted_mergeSort'` even when row words repeat.

**C.28 — `occupied_card_reindex`.** For every `N`, `R : Fin N → List ℕ`, `e : Equiv.Perm (Fin N)`, and arbitrary `xList : List ℕ`,

`(occupied N (rowsOfLabels (R ∘ e)) xList).card = (occupied N (rowsOfLabels R) xList).card`.

**C.29 — `collisionPairs_card_reindex`.** For the same parameters,

`(collisionPairs N (rowsOfLabels (R ∘ e)) xList).card = (collisionPairs N (rowsOfLabels R) xList).card`.

Map the increasing pair `(i,j)` to the increasing rearrangement of `(e i,e j)`, using its minimum and maximum. The inverse uses `e.symm`. Split explicitly on which image label is smaller; injectivity rules out equality. This proof does not claim that individual adjacent edges or individual collision-pair position labels are invariant under sorting.

**C.30 — `sorted_occupancy_eq_raw`.** For every sample `ω` and arbitrary `xList : List ℕ`,

`occupancyCount N (sortedRows ω) xList = occupancyCount N (rawRows ω) xList`.

**C.31 — `sorted_collisionPairs_card_eq_raw`.** For every sample `ω` and arbitrary `xList : List ℕ`,

`(collisionPairs N (sortedRows ω) xList).card = (collisionPairs N (rawRows ω) xList).card`.

### Exact product events and expected counts

**C.32 — `matrix_prefix_probability`.** For every `i : Fin N`,

`(matrixLaw n hn).probability (fun ω => prefixWord x <+: rawRow ω i) = prefixMass n hM x`.

This is for a fixed original row label, before sorting. It does not assert that a fixed sorted row position has the same prefix probability.

**C.33 — `matrix_pair_prefix_probability`.** For `i j : Fin N` and `hij : i ≠ j`,

`(matrixLaw n hn).probability (fun ω => rawRow ω i = rawRow ω j ∧ prefixWord x <+: rawRow ω i)`

`= prefixPairFactor n hM x * tailCollisionFactor n M`.

Split columns into indices `<M` and `≥M`: the first require both labels to have the prescribed digit; the latter require their digits to agree. C.03/C.04 and C.14/C.15 give the product. Empty parts have probability and product one.

**C.34 — `matrix_expected_raw_occupancy`.** For all `N` including zero,

`(matrixLaw n hn).expectation (fun ω => (occupancyCount N (rawRows ω) (prefixWord x) : ℝ)) = prefixMean n hM x`.

**C.35 — `matrix_expected_sorted_occupancy`.** Replace `rawRows` by `sortedRows` in C.34, with the same right side. Derive it from C.30 and C.34.

**C.36 — `collisionPairs_subset_increasing`.** For every `N`, arbitrary `rows : ℕ → List ℕ`, and arbitrary `xList`,

`collisionPairs N rows xList ⊆ ((range N) ×ˢ (range N)).filter (fun p => p.1 < p.2)`.

**C.37 — `increasing_pair_card`.** For every `N`,

`(((range N) ×ˢ (range N)).filter (fun p => p.1 < p.2)).card = Nat.choose N 2`.

This includes `N=0,1` and avoids any ambiguous division in the finite indexing count.

**C.38 — `matrix_expected_raw_collisionPairs`.** For all `N`,

`(matrixLaw n hn).expectation (fun ω => ((collisionPairs N (rawRows ω) (prefixWord x)).card : ℝ))`

`= (Nat.choose N 2 : ℝ) * prefixPairFactor n hM x * tailCollisionFactor n M`.

Use existing F12, C.36–C.37 and the event formula C.33. In particular, the right side is zero for `N≤1` even when prefix or tail products are empty. A separate branch must dispose of those deck sizes before invoking a distinct-label statement.

**C.39 — `matrix_expected_sorted_collisionPairs`.** Replace `rawRows` by `sortedRows` in C.38, retaining the same right side. Derive it using the samplewise equality C.31.

### Arithmetic and final internal density estimates

**C.40 — `singleFactor_nonneg`.** For all `N k n a`, `0 ≤ singleFactor N n a`.

**C.41 — `pairFactor_nonneg`.** For all `N k n a b`, `0 ≤ pairFactor N n a b`. There is no sum-of-counts hypothesis for nonnegativity.

**C.42 — `pairFactor_same_le_singleFactor_sq`.** For `N k n h`, `hN : 2 ≤ N`, and `a : Fin k`,

`pairFactor N n a a ≤ (singleFactor N n a)^2`.

Use `n a ≤ N` and split `n a=0`, `n a=1`, and `n a≥2` if needed to keep the natural subtraction/casts explicit. The actual probability bound is proved from arithmetic; it is not an input to the column law. This inequality is also numerically true for `N=0,1`, but the proposed helper only uses the branch with a positive two-row denominator; the final theorems cover the other branches directly.

**C.43 — `prefix_factors_nonneg`.** For the matrix and prefix data, each of `prefixMass n hM x`, `prefixPairFactor n hM x`, and `prefixMean n hM x` is nonnegative. This is one theorem with three conjuncts.

**C.44 — `tail_factors_nonneg`.** For the matrix data and arbitrary `M`, both `tailCollisionFactor n M` and `tailSquareFactor n M` are nonnegative.

**C.45 — `prefixPairFactor_le_prefixMass_sq`.** For the matrix and prefix data and `hN : 2 ≤ N`,

`prefixPairFactor n hM x ≤ (prefixMass n hM x)^2`.

**C.46 — `tailCollisionFactor_le_tailSquareFactor`.** For the matrix data, arbitrary `M`, and `hN : 2 ≤ N`,

`tailCollisionFactor n M ≤ tailSquareFactor n M`.

This is the exact finite inequality later corresponding to `q_tail ≤ N^{c_E}`. This additive contract does not introduce logarithms, asymptotic exponents, or a theorem about their approximation.

**C.47 — `internal_density_le_sq_expected_edges`.** For arbitrary existing `w : FiniteLaw Ω`, `[Fintype Ω]`, `N : ℕ`, `R : Ω → ℕ → List ℕ`, and `xList : List ℕ`,

`edgeDensity w N R xList ≤ (w.expectation (fun ω => (edgeCount N (R ω) xList : ℝ)))^2`.

Use existing F12 for the sum of edge probabilities and the trusted `Finset.sum_sq_le_sq_sum_of_nonneg`, with nonnegativity supplied by existing F04. No row sorting or matrix model is required by this generic inequality. It is a new proved consequence of the existing definitions, not a modification of F22.

**C.48 — `collisionPairs_zero`.** For arbitrary `rows : ℕ → List ℕ` and `xList`, `collisionPairs 0 rows xList = ∅`.

**C.49 — `collisionPairs_one`.** For arbitrary `rows : ℕ → List ℕ` and `xList`, `collisionPairs 1 rows xList = ∅`.

These permit explicit `N=0,1` branches in count and arithmetic theorems. Existing F17–F18 already give the analogous internal-edge cases.

**C.50 — `matrix_expected_collisionPairs_le_tight_mean_bound`.** For all matrix and prefix data, including `N=0,1`, let the displayed quantities mean the existing definitions, and assert

`(matrixLaw n hn).expectation (fun ω => ((collisionPairs N (sortedRows ω) (prefixWord x)).card : ℝ))`

`≤ (((N - 1 : ℕ) : ℝ) / (2 * (N : ℝ))) * (prefixMean n hM x)^2 * tailCollisionFactor n M`.

For `N≥2`, substitute C.39 and C.45 and the identity `(N choose 2) = N(N−1)/2`. For `N=0,1`, prove both sides are zero from C.48–C.49 and the definitions. Division by zero is never used to derive a probability identity; the all-size statement uses Lean's total real division and explicit zero branches.

**C.51 — `matrix_expected_collisionPairs_le_half_mean_bound`.** With the same universal parameters,

`E[#collisionPairs(sortedRows,prefixWord x)] ≤ (prefixMean n hM x)^2 * tailCollisionFactor n M / 2`.

Derive the coefficient bound from C.50 and nonnegative factors, treating `N=0` separately. The proof's extra case splits are not extra assumptions in the theorem.

**C.52 — `matrix_expected_internal_edges_le_half_mean_bound`.** With the same universal parameters,

`E[edgeCount N (sortedRows ω) (prefixWord x)] ≤ (prefixMean n hM x)^2 * tailCollisionFactor n M / 2`.

The expectation is under `matrixLaw n hn`. Combine existing F24 with C.51.

**C.53 — `matrix_internal_density_le_collision_square`.** With the same universal parameters,

`edgeDensity (matrixLaw n hn) N sortedRows (prefixWord x)`

`≤ ((Nat.choose N 2 : ℝ) * prefixPairFactor n hM x * tailCollisionFactor n M)^2`.

Combine C.47, existing F24, and C.39. Use nonnegative expectations before squaring the comparison.

**C.54 — `matrix_internal_density_le_mean_tail_fourth`.** With the same universal parameters,

`edgeDensity (matrixLaw n hn) N sortedRows (prefixWord x)`

`≤ (prefixMean n hM x)^4 * (tailCollisionFactor n M)^2 / 4`.

Combine C.47 and C.52 using nonnegative factors. This is the exact finite `μ_x^4 q_tail^2/4` statement. It has no small-block hypothesis and no `c_F` factor.

**C.55 — `matrix_internal_density_le_prefixMean`.** With the same universal parameters,

`edgeDensity (matrixLaw n hn) N sortedRows (prefixWord x) ≤ prefixMean n hM x`.

Combine existing F23 with C.35. This is the terminal singleton's finite probabilistic content, valid also for shorter prefixes and without a small-mean condition. No modification of the already frozen F23 is required.

**C.56 — `tailCollisionFactor_at_full_length`.** For every matrix data set, `tailCollisionFactor n K = 1`.

**C.57 — `prefix_factors_empty`.** For the unique `x : Fin 0 → Fin k` and any proof `0 ≤ K`, `prefixWord x = []`, `prefixMass n hM x = 1`, and `prefixPairFactor n hM x = 1`. This is one theorem with three conjuncts.

The preferred final named inventory therefore consists of C.01–C.57, with C.20 split into the two explicitly named declarations above. There is no planned `expectation_finset_sum` wrapper: the existing F12 and local finite-sum manipulations suffice for these proofs. If a reviewer selects such a named helper for clarity before freeze, its exact signature should be added to the additive contract then; it must not appear later as an unreviewed declaration.

## 4. Dependency order

1. C.D01–C.D02 and C.01–C.05 use the existing `FiniteLaw` definitions and trusted finite sum/product results.
2. C.06–C.11 justify the fixed-column subtype's inhabitance, reindexing equivalence and deterministic counts.
3. C.12–C.15 prove exchangeability and one-/two-label probabilities. C.16 treats zero piles directly. C.17 proves the matrix product law agrees with uniform matrices.
4. C.18–C.23 connect vector words and the raw matrix to the frozen list-prefix definitions.
5. C.25 gives C.24 and C.26, which justify `sortPermutation` using the trusted index equivalence. C.27 certifies sortedness. C.28–C.29 yield C.30–C.31.
6. C.32–C.33 follow from column probabilities and product events. C.34–C.39 follow by summing one- and two-label indicators and then transporting counts through sorting.
7. C.40–C.46 supply nonnegativity and the without-replacement comparison. C.48–C.49 separately dispose of zero-/one-card collision cases.
8. C.47 plus the previously frozen F24 and the new exact count/arithmetic results prove C.50–C.55. C.56–C.57 simplify terminal and empty-prefix cases.

The chronological order of declarations can differ from their numbering to respect these dependencies. In particular, C.25 must precede a definition that uses the length obtained from it, C.48–C.49 should be available before all-size expected-count formulas, and constructor proofs are written only after their deterministic ingredients exist.

## 5. Complete degenerate-case audit

**`N=0`.** Every `FixedColumn` allowed by the sum condition has all counts zero and its domain is empty. Its uniform law exists; no row digit is chosen. The matrix product exists even for zero alphabet. All frozen occupied, collision and edge sets are empty. `prefixMean=0`, and every final expectation/density inequality has zero left side. One-/two-label formulas have no applicable row labels. Empty products remain one rather than being assigned an artificial zero value.

**`N=1`.** Each column has exactly one entry. No distinct label pair exists, C.49 makes collision counts zero, and frozen F18 makes all internal-edge densities zero. One-label and occupancy formulas remain exact. Pair factors have denominator zero and value zero; they are used only in all-size formulas multiplied by `choose 1 2=0`, or in inequalities whose zero case is proved separately.

**`k=0`.** If `K>0`, choose an actual column index; its sum condition forces `N=0`. If `K=0`, the condition is vacuous and arbitrary `N` is allowed. Since `M≤K`, the prefix is then empty, all rows are empty words, and the graph has exactly `N-1` deterministic path edges. The law on the empty family of columns is the one-point law. These cases require neither `Nonempty (Fin k)` nor a default digit.

**`K=0`, any alphabet.** `M=0`, all raw/sorted rows are `[]`, both prefix factors and the tail factor are one, expected occupancy is `N`, and expected collisions are `choose N 2`. The exact formulas therefore remain correct. The actual density is `N-1`, consistent with every displayed upper bound, including `N=0,1` via natural subtraction.

**`M=0`.** C.57 gives the empty prefix and prefix factors one. No prefix-digit probability is invoked. Tail equality across all columns supplies the collision factor.

**`M=K`.** C.56 gives the empty tail product one. C.33 becomes the probability that both labels equal the fixed full word. C.55 supplies the direct terminal bound.

**A zero selected prefix pile.** C.16 makes that digit impossible for every matrix sample; both prefix factors are zero, occupancy and collisions are identically zero, and all corresponding expectations vanish. This case is included rather than excluded by a legal-word assumption.

**A selected prefix pile of size one.** Its two-row factor is zero. Exact C.38–C.39 gives expected collisions zero, and C.53 gives density zero. A single occupied row may still exist; the one-row formula is not set to zero.

**A zero tail coincidence factor.** C.D13 gives tail product zero. C.38–C.39 and C.53 give zero collision expectation and density. No reciprocal tail factor is used anywhere.

**Repeated full words and arbitrary ties in sorting.** The list of row labels is still a permutation with no duplicate labels. C.29 orients image pairs explicitly by minimum/maximum. Therefore no assumption that rows are distinct and no choice of tie order enters any count formula.

**A prefix list longer than `K` or containing a digit outside `Fin k`.** These are outside the source's word domain and outside the matrix-prefix quantified statement. C.23 does encode every in-alphabet list, even an overlong one; applying a matrix-prefix theorem additionally requires the length bound `M≤K`, which an overlong list cannot satisfy. C.23 does not encode an out-of-alphabet digit. The generic frozen deck lemmas still apply to both kinds of list. In contrast, zero-count in-alphabet digits are included explicitly in the matrix-prefix results above.

**Ambient translation and conditioning.** Sorting and label reindexing preserve the total collision count and occupied count. They do not preserve edge locations or squared edge probabilities. This contract states absolute-coordinate density for the defined sorted deck. It does not assert equality with a randomly recentered density, and it does not assume that an exploration-conditioned law is independent uniform columns. Those remain separately reviewed mathematical obligations.

## 6. Scope of what would be proved after an additive freeze

The proposed module would establish an actual explicit finite model, exact single- and double-row probabilities, the exact expected collision-pair formula, and internal shuffle-graph bounds under that model. All construction fields are either deterministic pile data or the already frozen definition of a normalized finite law. The probability formulas and all bounds are outputs.

The proposal preserves all original source assumptions by proving these finite consequences for a larger deterministic domain. It does not freeze an alternative asymptotic `c_F` statement. Passing to logarithmic exponents, proving stable-profile class bounds, or identifying a conditioned residual law still requires separately reviewed and frozen statements. The existing v1 contract stays byte-identical.

## 7. Separate optional extension: division-free occupancy conditioning

This section is a complete additional design for review, **outside the proposed core inventory C.D01–C.D14/C.01–C.57 unless the independent comparison explicitly accepts it**. It should not delay freezing the core. It addresses the finite conditional internal-edge component, without purporting to establish the exploration-conditioned residual model at TeX lines 1923–1943.

The desired event is conditioning only on the number of rows carrying the fixed prefix. For a fixed prefix this event depends only on the prefix columns. The remaining columns are still independent under the original model. A division-free theorem expresses that fact without assuming positive probability of the conditioning event or defining conditional probability at a null event.

### Explicit additional definitions

**O.D01 — `prefixCounts` and `suffixCounts`.** For the same `n` and `hM : M ≤ K`,

- `prefixCounts n hM : Fin M → Fin k → ℕ` is `fun t => n ⟨t.val, t.isLt.trans_le hM⟩`;
- `suffixCounts n hM : Fin (K-M) → Fin k → ℕ` is `fun t => n ⟨M+t.val, by arithmetic from hM and t.isLt⟩`.

Both have total `N` at every coordinate by `hn`. There is no new pile assumption. Apply the existing `matrixLaw` definition to these data to obtain the prefix law and tail law; no new law constructor is needed.

**O.D02 — `splitMatrix`.** Define the equivalence

`FixedMatrix N K k n ≃ (FixedMatrix N M k (prefixCounts n hM)) × (FixedMatrix N (K-M) k (suffixCounts n hM))`

by restriction to the two coordinate intervals. Its inverse evaluates the prefix array when `j.val<M`, and the tail array at `j.val-M` otherwise. Equality of the appropriate count functions is handled by the explicit coordinate maps and dependent transports. The inverse/equivalence laws are constructor proof obligations from those maps, not hypotheses.

In the statements below write `glue(p,t) = (splitMatrix n hM).symm (p,t)`. This is notation for the existing equivalence's inverse, not another definition. Write `W`, `Wpre`, and `Wtail` for the three explicit matrix laws, and write `Z(ω) = occupancyCount N (sortedRows ω) (prefixWord x)`. This too is local notation, not an extra random-variable assumption or structure field.

### Complete additional lemma inventory

**O.01 — `matrix_expectation_split`.** For every `f : FixedMatrix N K k n → ℝ`,

`W.expectation f = Wpre.expectation (fun p => Wtail.expectation (fun t => f (glue(p,t))))`.

This follows by reindexing the finite sum through O.D02 and splitting the explicit product weights. This is the actual model's factorization theorem; it does not assume conditional independence.

**O.02 — `tailCollisionFactor_suffix`.**

`tailCollisionFactor (suffixCounts n hM) 0 = tailCollisionFactor n M`.

Prove it by the bijection between `Fin(K-M)` and the suffix index finset, including `M=K`.

**O.03 — `prefix_occupancy_glue`.** For every prefix array `p` and tail array `t`,

`occupancyCount N (rawRows (glue(p,t))) (prefixWord x) = occupancyCount N (rawRows p) (prefixWord x)`.

The right side is a matrix with exactly `M` columns. A full word of length `M` has prefix `prefixWord x` precisely when it equals that word. Together with C.30 this proves that `Z(glue(p,t))` is independent of `t` as a deterministic function, not as an assumed probabilistic property.

**O.04 — `increasing_pairs_in_finset_card`.** For every `s : Finset ℕ`,

`((s ×ˢ s).filter (fun p => p.1 < p.2)).card = Nat.choose s.card 2`.

This generalizes C.37 from the full label set to an arbitrary fixed subset of labels. If this optional section is adopted, C.37 can be proved as its range specialization; it need not be removed from the core inventory.

**O.05 — `tail_expected_collisionPairs_given_prefix_array`.** For every fixed prefix array `p`,

`Wtail.expectation (fun t => ((collisionPairs N (sortedRows (glue(p,t))) (prefixWord x)).card : ℝ))`

`= (Nat.choose (occupancyCount N (rawRows p) (prefixWord x)) 2 : ℝ) * tailCollisionFactor n M`.

The occupied original-label subset is now deterministic. Each increasing pair in it collides precisely when its two tail words agree. C.33 for the suffix matrix and empty prefix gives that tail probability; O.02 identifies its factor; O.04 counts the pairs. C.31 transports the collision count through full-word sorting. For `N≤1`, the label subset has no pair and the proof uses that empty case before a two-label formula.

**O.06 — `matrix_collisionPairs_occupancy_slice`.** For every `q : ℕ`, with no condition on `q` or the slice probability,

`W.expectation (fun ω => if Z(ω)=q then ((collisionPairs N (sortedRows ω) (prefixWord x)).card : ℝ) else 0)`

`= (Nat.choose q 2 : ℝ) * tailCollisionFactor n M * W.probability (fun ω => Z(ω)=q)`.

Apply O.01. By O.03, the indicator is fixed when integrating tail columns. O.05 supplies the count, and on the indicator's true branch its binomial coefficient is `choose q 2`. The false branch is zero. This equality is the exact division-free conditional collision formula.

**O.07 — `matrix_internal_edges_occupancy_slice`.** For every `q : ℕ`,

`W.expectation (fun ω => if Z(ω)=q then (edgeCount N (sortedRows ω) (prefixWord x) : ℝ) else 0)`

`≤ (Nat.choose q 2 : ℝ) * tailCollisionFactor n M * W.probability (fun ω => Z(ω)=q)`.

This is pointwise frozen F21 on the true branch, zero on the false branch, followed by expectation monotonicity and O.06. It is not a replacement definition of a conditional law.

### Additional case and scope checks

- A zero-probability occupancy slice causes both sides of O.06 to vanish; no division is taken.
- `q=0,1` gives no pair and zero internal edges on the slice.
- `q>N` is impossible because occupied labels form a subset of the `N` labels. O.06–O.07 remain valid without adding `q≤N`.
- `M=0` gives the deterministic occupied count `N`; the prefix-array space is the unique empty array.
- `M=K` gives the unique empty tail array and tail factor one.
- `N=0,1`, an empty alphabet, and zero piles have exactly the core cases from section 5. O.D02 splits empty coordinate families as actual empty functions.
- O.06–O.07 concern occupancy conditioning for a fixed deterministic prefix under the original unconditioned matrix law. They do not assert that arbitrary revealed strings or arbitrary exploration sigma-fields leave a product column law.

If this optional extension is selected for the additive freeze, its additional definitions and O.01–O.07 must be included in the same independent comparison before implementation. If it is not selected, this finite conditional component remains outstanding and must not be counted as verified.

## 8. Final signature and module policy for the selected core

The root comparison selected **only C.D01–C.D14 and C.01–C.57, including C.20a and C.20b**. Section 7's optional definitions and O.01–O.07 are excluded from this additive freeze. They remain an outstanding finite conditional component. This section removes notational shorthand and organizational ambiguity from the preceding mathematical specifications; it does not change any proposition.

### Namespaces and arguments

All new declarations are in namespace `EdgeLocalization`, except the two law constructors and C.01–C.05, which are in its existing nested namespace `FiniteLaw`, and the reindexing equivalence, which is in `EdgeLocalization.FixedColumn`. The directory component `Collision` is a module path, not an additional Lean namespace.

The following argument lists are fixed. Braces indicate implicit parameters; parentheses indicate explicit parameters. The expressions below specify signatures only; they are not implementation bodies.

| Definition or instance | Fixed argument order and result type |
|---|---|
| `FiniteLaw.uniform` | `(Ω : Type u) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω` |
| `FiniteLaw.pi` | `{ι : Type u} [Fintype ι] {Ω : ι → Type v} [∀ j, Fintype (Ω j)] (w : ∀ j, FiniteLaw (Ω j)) : FiniteLaw (∀ j, Ω j)` |
| `FixedColumn` | `(N k : ℕ) (n : Fin k → ℕ) : Type` |
| `fixedColumnFintype` | `(N k : ℕ) (n : Fin k → ℕ) : Fintype (FixedColumn N k n)` |
| `FixedColumn.reindex` | `{N k : ℕ} (n : Fin k → ℕ) (π : Equiv.Perm (Fin N)) : FixedColumn N k n ≃ FixedColumn N k n` |
| `columnLaw` | `{N k : ℕ} (n : Fin k → ℕ) (h : ∑ a, n a = N) : FiniteLaw (FixedColumn N k n)` |
| `FixedMatrix` | `(N : ℕ) {K k : ℕ} (n : Fin K → Fin k → ℕ) : Type` |
| `fixedMatrixFintype` | `(N : ℕ) {K k : ℕ} (n : Fin K → Fin k → ℕ) : Fintype (FixedMatrix N n)` |
| `matrixLaw` | `{N K k : ℕ} (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N) : FiniteLaw (FixedMatrix N n)` |
| `prefixWord` | `{M k : ℕ} (x : Fin M → Fin k) : List ℕ` |
| `rawRow` | `{N K k : ℕ} (n : Fin K → Fin k → ℕ) (ω : FixedMatrix N n) (i : Fin N) : List ℕ` |
| `rowsOfLabels` | `{N : ℕ} (R : Fin N → List ℕ) : ℕ → List ℕ` |
| `rawRows` | `{N K k : ℕ} (n : Fin K → Fin k → ℕ) (ω : FixedMatrix N n) : ℕ → List ℕ` |
| `sortedLabels` | `{N : ℕ} (R : Fin N → List ℕ) : List (Fin N)` |
| `sortPermutation` | `{N : ℕ} (R : Fin N → List ℕ) : Equiv.Perm (Fin N)` |
| `sortedRows` | `{N K k : ℕ} (n : Fin K → Fin k → ℕ) (ω : FixedMatrix N n) : ℕ → List ℕ` |
| `singleFactor` | `(N : ℕ) {k : ℕ} (n : Fin k → ℕ) (a : Fin k) : ℝ` |
| `pairFactor` | `(N : ℕ) {k : ℕ} (n : Fin k → ℕ) (a b : Fin k) : ℝ` |
| `coincidenceFactor` | `(N : ℕ) {k : ℕ} (n : Fin k → ℕ) : ℝ` |
| `prefixMass` | `(N : ℕ) {K k M : ℕ} (n : Fin K → Fin k → ℕ) (hM : M ≤ K) (x : Fin M → Fin k) : ℝ` |
| `prefixPairFactor` | `(N : ℕ) {K k M : ℕ} (n : Fin K → Fin k → ℕ) (hM : M ≤ K) (x : Fin M → Fin k) : ℝ` |
| `tailCollisionFactor` | `(N : ℕ) {K k : ℕ} (n : Fin K → Fin k → ℕ) (M : ℕ) : ℝ` |
| `tailSquareFactor` | `(N : ℕ) {K k : ℕ} (n : Fin K → Fin k → ℕ) (M : ℕ) : ℝ` |
| `prefixMean` | `(N : ℕ) {K k M : ℕ} (n : Fin K → Fin k → ℕ) (hM : M ≤ K) (x : Fin M → Fin k) : ℝ` |

In particular, the count array's type does **not** determine the population `N`. That is why `N` is explicit in `FixedMatrix` and every scalar factor. In `columnLaw` and `matrixLaw`, the explicit sum proof determines it. In the row adapters, the sample's type determines it. All occurrences earlier in this report of `rawRow ω`, `rawRows ω`, and `sortedRows ω` abbreviate `rawRow n ω`, `rawRows n ω`, and `sortedRows n ω`. All occurrences of the multi-column scalar factors abbreviate the same factor with its explicit first argument `N`.

For theorem parameters, infer natural sizes from the typed data where possible, and otherwise leave the size explicit:

- Column probability theorems use `{N k : ℕ} (n : Fin k → ℕ) (h : ∑ a, n a = N)`, followed by the explicitly listed labels, digit(s), and inequality proof. C.08 and C.10, which take an actual typed column, infer sizes from that column. C.40–C.42 retain the explicit `N` needed by their scalar factors; C.42 still has the explicit sum proof and `hN : 2 ≤ N`.
- Matrix probability/expectation theorems use `{N K k M : ℕ} (n : Fin K → Fin k → ℕ) (hn : ∀ j, ∑ a, n j a = N) (hM : M ≤ K) (x : Fin M → Fin k)`, followed by any explicitly stated label(s) and inequality proof. Omit `M hM x` when the theorem does not mention a prefix. The main end-to-end theorems do not acquire `hN : 2 ≤ N`; they cover all `N` as specified.
- Pure nonnegativity of prefix/tail expressions C.43–C.44 needs the sizes, `n`, and `hM/x` or `M` occurring in those expressions, but **does not take `hn`** because no feasibility condition is used or stated by their algebraic content. C.43 uses `(N : ℕ) {K k M : ℕ} (n ...) (hM ...) (x ...)`; C.44 uses `(N : ℕ) {K k : ℕ} (n ...) (M : ℕ)`. Likewise C.56–C.57 are definitional empty-product statements and do not take `hn`. C.45–C.46 do take `hn` and their stated `hN`.
- The generic row-count, sorting, and finite-law theorems retain exactly their domains in section 3. They do not take `hn`, a matrix sample, or any other irrelevant parameter unless their statement actually uses it.
- The two finite instances listed in the table are the only planned named custom instances. Nonempty fixed-column instances inside constructors are local instances of the proved C.06 result. Decidability and finite subtype/function instances otherwise use existing inferred instances or local classical instances.

The `FiniteLaw` universe parameters remain fully generic, as in the existing file. Matrix/sample types use ordinary finite types. No dependent equality proof is mathematical model data: bounds for the initial-segment embedding and list indices are generated from the stated natural inequalities.

### Selected module allocation

All paths below are relative to `lean/EdgeLocalization/EdgeLocalization`.

| Module | Selected declarations |
|---|---|
| `Collision/FiniteLaw.lean` | C.D01–C.D02; C.01–C.05. Imports the existing frozen `EdgeLocalization.FiniteLaw`. |
| `Collision/Column.lean` | C.D03–C.D05 and C.D12, including `fixedColumnFintype`; C.06–C.16 and C.40–C.42. Imports `Collision.FiniteLaw`. The histogram and nonempty theorems precede definitions whose proof terms require them. |
| `Collision/Model.lean` | C.D06–C.D08 and C.D13–C.D14, including `fixedMatrixFintype`. Thus `FixedMatrix`, `matrixLaw`, vector/list prefix conversion, raw row adapters, and all multi-column factors are available without importing sorting or probability estimates. Imports `Collision.Column`. |
| `Collision/Rows.lean` | C.D09–C.D11; C.18–C.31 including C.20a/C.20b, plus C.36–C.37 and C.48–C.49. Imports `Collision.Model` and frozen `EdgeLocalization.Deck`. |
| `Collision/Matrix.lean` | C.17; C.32–C.35; C.38–C.39; C.43–C.46; C.56–C.57. Imports `Collision.Rows`. The expectation formulas use the already available row and collision-count bridges. |
| `Collision/Estimates.lean` | C.47 and C.50–C.55. Imports `Collision.Matrix` and frozen `EdgeLocalization.Density`. |

This is a directed dependency graph: `FiniteLaw → Column → Model → Rows → Matrix → Estimates`. The module allocation does not reorder the logical dependencies within each module. No existing finite module is overwritten; new files import the previously proved statements.

## 9. Independent comparison and acceptance

After completing sections 1–7 independently, I read both `collision_contract_reconstruction.md` and `collision_contract_assumptions.md`. Their model and mathematical conclusions agree with the selected core:

- All three reports use the actual fixed-count assignment spaces and derive uniformity/exchangeability; none substitutes independent rows or a common permutation of all columns.
- The reconstruction's uniform law on the entire product and this report's product of uniform column laws are identified by C.17's exact weight formula. This is a proved comparison, not a new model hypothesis.
- Both other reports confirm the one-/two-label averaging proofs, including the distinction between ordered `N(N−1)` denominators and unordered `choose N 2` counts. The reconstruction supplies an explicit two-swap construction that proves C.11 without four-distinct-label assumptions.
- Both endorse sorting original labels and the pointwise invariance of collision/occupancy cardinalities. The selected concrete list-index equivalence removes the reconstruction report's optional choice-based sorting definition; the semantic sorted-deck property is the same and is proved by C.27.
- Their exact expected collision formula and `μ^4 q^2/4` endpoint agree with C.38–C.54. The selected core additionally retains the correct tighter coefficient, the prefix-mean density bound, and the full two-digit request formula as explicitly proved statements.
- Every degenerate case identified by the assumptions report is addressed in section 5. Its correction concerning C.23 and overlong in-alphabet lists has been incorporated: encoding a list does not establish the separate bound `M≤K` required by a matrix theorem.
- The optional occupancy-slice formula from the assumptions report is mathematically sound and is specified in section 7, but the root selected it outside this additive freeze. The core must not be reported as having proved it or an exploration-conditioned law.

I accept the selected core's mathematical domains, definitions, quantified statements, dependency order, and signature policy for additive freezing. There is no remaining mathematical mismatch among the three independent reports. Trusted API details may affect local proof terms, but not the definitions' semantics or any hypothesis/conclusion. The source files and the v1 frozen contract have not been modified.
