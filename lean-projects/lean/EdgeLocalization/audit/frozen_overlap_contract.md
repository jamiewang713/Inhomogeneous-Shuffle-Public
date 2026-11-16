# Frozen additive independent-copy overlap contract

This contract is frozen before any Overlap Lean code. It selects exactly the single definition S.D01 and the six statements S.01–S.06 reproduced below, with their precise signatures and semantics. All three independent reports were compared, each reviewer accepted the final complete signatures, and the root comparison is recorded in overlap_contract_comparison.md.

All earlier definitions, theorem statements, proofs, and freezes remain unchanged. No new assumption, changed conclusion, extra named helper, new custom instance, extra axiom, or unproved placeholder is permitted. Local proved steps and trusted mathlib results may implement the listed dependencies. The module allocation is Overlap/FiniteLaw.lean for S.D01/S.01–03 and Overlap/Edges.lean for S.04–06. The original full goal remains active and incomplete.

The exact inventory follows. Its pre-freeze wording is preserved as the statement specification selected by this freeze.

# Proposed additive contract for expected shared internal edges

This is an independent statement-design report for comparison before a new freeze. It proposes one definition and exactly six theorems. It changes no existing definition, assumption, theorem, source file, implementation, or frozen report. No Lean implementation is authorized before comparison and freeze.

## 1. Source and precise scope

I reread the permitted TeX at lines 1800–1865, including the displayed identity at 1837–1841. The proposition explicitly uses two independent shuffle graphs at 1827–1832. Its initial identity expresses the expected number of common adjacent edges as the sum of squared one-copy edge probabilities.

I also reread the permitted `2103.05068v3.pdf` extraction at lines 335–375 and 397–423: page 7 states the same exact identity, and page 8 specifies that primed objects are independent copies. Page 23, Lemma 4.11 and its proof, then use the blockwise squared probabilities in the localization argument. Page 30, Lemma 5.2 and its proof, use the more general identity `E|A∩B| = Σ_i P(i∈A)P(i∈B)` before applying AM–GM. The permitted `2510.22783v1.pdf`, page 34, Lemma 5.2 repeats that independent-subset comparison.

The new addendum formalizes the exact finite overlap identity and transfers two already proved actual-matrix density estimates through it. It does not assert the source's asymptotic first-moment bound, AM–GM localization, conditional independent-copy identities, or exploration estimates. In particular it supplies no missing spatial spread hypothesis or estimate.

## 2. Data and namespace conventions

The generic laws use independent universe-polymorphic types `Ω : Type*` and `Λ : Type*`, each with its existing `Fintype` instance. Their laws are explicit arguments `w : FiniteLaw Ω` and `v : FiniteLaw Λ`. There is no separate `Nonempty`, uniformity, positivity-of-weights, or independence premise. Independence is realized by the newly constructed product law.

For finite random subsets, `α : Type*` has only `[DecidableEq α]`, not a `Fintype` requirement. The deterministic common support is `s : Finset α`. Random subsets are explicit functions `H : Ω → Finset α` and `J : Λ → Finset α`, with pointwise support hypotheses `hH : ∀ ω, H ω ⊆ s` and `hJ : ∀ λ, J λ ⊆ s`. These hypotheses state the prescribed finite support; they do not assume an intersection or probability conclusion. Both are retained as requested even though containment of either set alone would suffice to locate its intersection in `s`.

The generic internal-edge identity uses explicit `N : ℕ`, `R : Ω → ℕ → List ℕ`, and `xList : List ℕ`. It requires no sorting or fixed row-length premise: the identity applies to the existing `internalEdges` definition for every such row family.

The actual-matrix specializations use exactly the existing data:

- implicit `N K k M : ℕ`;
- explicit `n : Fin K → Fin k → ℕ`;
- explicit `hn : ∀ j : Fin K, ∑ a : Fin k, n j a = N`;
- explicit `hM : M ≤ K`;
- explicit `x : Fin M → Fin k`.

All existing meanings remain unchanged: `matrixLaw n hn` is the product of independent uniform prescribed-count columns; `sortedRows n ω` is the sorted deck for one matrix outcome; `prefixWord x` is the source prefix list; `prefixMean N n hM x` and `tailCollisionFactor N n M` retain the original population `N`. The two copies have the same deterministic pile array, the same prefix, and independently drawn matrix outcomes.

The definition and generic probability theorems are in namespace `EdgeLocalization.FiniteLaw`. The three edge theorems are in namespace `EdgeLocalization`. `Overlap` is a module directory, not a further namespace.

## 3. Complete definition inventory

### S.D01 — `EdgeLocalization.FiniteLaw.prod`

Exact signature:

`{Ω Λ : Type*} [Fintype Ω] [Fintype Λ] (w : FiniteLaw Ω) (v : FiniteLaw Λ) : FiniteLaw (Ω × Λ)`.

Its weight must be definitionally

`(w.prod v).weight z = w.weight z.1 * v.weight z.2`.

The nonnegativity and total-mass fields are proved in the constructor. The total-mass proof is the finite product-sum identity together with `w.total` and `v.total`; it does not accept normalization of the proposed product as a hypothesis. The trusted product `Fintype` instance is used. There is no new named instance or named normalization lemma.

## 4. Complete theorem inventory

### S.01 — `EdgeLocalization.FiniteLaw.prod_expectation`

Parameters, in order:

`{Ω Λ : Type*} [Fintype Ω] [Fintype Λ]`

`(w : FiniteLaw Ω) (v : FiniteLaw Λ) (f : Ω × Λ → ℝ)`.

Exact conclusion:

`(w.prod v).expectation f =`

`w.expectation (fun ω => v.expectation (fun λ => f (ω, λ)))`.

`f` is an arbitrary real-valued function. There is no nonnegativity, measurability, integrability, support, or boundedness premise; finite sums require none of those additional premises.

### S.02 — `EdgeLocalization.FiniteLaw.prod_probability`

Parameters, in order:

`{Ω Λ : Type*} [Fintype Ω] [Fintype Λ]`

`(w : FiniteLaw Ω) (v : FiniteLaw Λ) (A : Ω → Prop) (B : Λ → Prop)`.

Exact conclusion:

`(w.prod v).probability (fun z => A z.1 ∧ B z.2) =`

`w.probability A * v.probability B`.

No `DecidablePred` arguments are added. The implementation can use local classical decisions as in the existing `probability` definition. The statement concerns events in the constructed product law, so it does not assume independence of arbitrary correlated variables.

### S.03 — `EdgeLocalization.FiniteLaw.expected_card_intersection`

Parameters, in order:

`{Ω Λ : Type*} [Fintype Ω] [Fintype Λ]`

`(w : FiniteLaw Ω) (v : FiniteLaw Λ)`

`{α : Type*} [DecidableEq α] (s : Finset α)`

`(H : Ω → Finset α) (J : Λ → Finset α)`

`(hH : ∀ ω, H ω ⊆ s) (hJ : ∀ λ, J λ ⊆ s)`.

Exact conclusion:

`(w.prod v).expectation (fun z => ((H z.1 ∩ J z.2).card : ℝ)) =`

`∑ i ∈ s, w.probability (fun ω => i ∈ H ω) *`

`  v.probability (fun λ => i ∈ J λ)`.

All intersections are intersections of finite sets of the same ambient labels. No correspondence or random relabeling is inferred. The support conditions hold pointwise, including at zero-weight outcomes.

### S.04 — `EdgeLocalization.edgeDensity_eq_expected_shared_internal_edges`

Parameters, in order:

`{Ω : Type*} [Fintype Ω] (w : FiniteLaw Ω)`

`(N : ℕ) (R : Ω → ℕ → List ℕ) (xList : List ℕ)`.

Exact conclusion:

`edgeDensity w N R xList =`

`(w.prod w).expectation (fun z =>`

`  ((internalEdges N (R z.1) xList ∩ internalEdges N (R z.2) xList).card : ℝ))`.

The common edge label is the same absolute zero-based left index in both copies. This matches the TeX's one-based adjacent pair `(m,m+1)` after `m=i+1`. The finite support is exactly `Finset.range (N - 1)`, with natural subtraction as in the existing definition of `edgeDensity`.

### S.05 — `EdgeLocalization.matrix_expected_shared_internal_edges_le_mean_tail_fourth`

Parameters, in order:

`{N K k M : ℕ} (n : Fin K → Fin k → ℕ)`

`(hn : ∀ j, ∑ a, n j a = N) (hM : M ≤ K) (x : Fin M → Fin k)`.

Exact conclusion:

`((matrixLaw n hn).prod (matrixLaw n hn)).expectation (fun z =>`

`  ((internalEdges N (sortedRows n z.1) (prefixWord x) ∩`

`    internalEdges N (sortedRows n z.2) (prefixWord x)).card : ℝ)) ≤`

`(prefixMean N n hM x) ^ 4 * (tailCollisionFactor N n M) ^ 2 / 4`.

This is exactly S.04 and the already proved `matrix_internal_density_le_mean_tail_fourth`. No small-mean, nonterminal-prefix, positive-tail-factor, or asymptotic premise is present.

### S.06 — `EdgeLocalization.matrix_expected_shared_internal_edges_le_prefixMean`

Parameters are exactly the same as S.05, in the same order.

Exact conclusion:

`((matrixLaw n hn).prod (matrixLaw n hn)).expectation (fun z =>`

`  ((internalEdges N (sortedRows n z.1) (prefixWord x) ∩`

`    internalEdges N (sortedRows n z.2) (prefixWord x)).card : ℝ)) ≤`

`prefixMean N n hM x`.

This is exactly S.04 and the already proved `matrix_internal_density_le_prefixMean`. It applies to every allowed prefix, including full-length prefixes, and does not impose the small-mean condition used in some source asymptotics.

## 5. Proof dependencies and local auxiliary steps

No additional named theorem, lemma, definition, abbreviation, or instance is proposed. Every new named declaration is listed above. The following auxiliary arguments belong inside those declarations as local proofs.

1. **S.D01:** prove product-weight nonnegativity with the two original law fields. Rewrite the sum over the product type as nested sums and factor a constant finite sum to prove normalization.
2. **S.01:** unfold the existing finite expectation and the new product weight; apply the trusted `Fintype.sum_prod_type`, then associate multiplication and use `Finset.mul_sum` termwise. Its proof does not need an extra finite-expectation linearity declaration.
3. **S.02:** apply S.01 to the conjunction indicator. For a fixed first outcome, split on `A ω`; in the true case the inner expectation is `v.probability B`, and in the false case it is zero. Factor the constant `v.probability B` from the remaining finite sum. Splits on `B λ`, if required to align indicator decisions, are local. Avoid expensive definitional equality of unrelated `Decidable` implementations; prove indicator equalities termwise instead.
4. **S.03:** apply the already proved `FiniteLaw.sum_probabilities_eq_expected_card` to `z ↦ H z.1 ∩ J z.2` on support `s`, in the equality's symmetric direction. Its support proof uses the two supplied subset facts (or either intersection projection). For each `i`, use `FiniteLaw.probability_congr` and `Finset.mem_inter` to expose a rectangle; S.02 evaluates its probability. This route needs no new finite-sum interchange lemma.
5. **S.04:** specialize S.03 with both laws `w`, both random subsets `internalEdges N (R ω) xList`, and support `Finset.range (N-1)`. Both subset premises are discharged by the existing `internalEdges_subset_range`. Reverse the resulting identity and use `edgeDensity`, `edgeProbability`, and `pow_two` to identify the sum of squares.
6. **S.05 and S.06:** rewrite the overlap expectation using S.04, then apply the corresponding existing matrix-density theorem. No new estimate or model fact is required.

The directed dependency order is

`S.D01 → S.01 → S.02 → S.03 → S.04 → {S.05, S.06}`,

with the existing expected-card lemma and deck support lemma entering S.03/S.04, and the already proved collision estimates entering S.05/S.06. The completed occupancy-conditioning addendum is not a dependency of these unconditional two-copy identities.

Proposed module ownership boundaries are `EdgeLocalization/Overlap/FiniteLaw.lean` for S.D01 and S.01–03, and `EdgeLocalization/Overlap/Edges.lean` for S.04–06. The first module needs the existing finite law and trusted finite product-sum APIs; the second imports it and `EdgeLocalization.Collision.Estimates`. Folder placement does not change the declared namespaces or arguments.

## 6. Complete boundary-case interpretation

- **`N = 0` or `N = 1`:** the existing internal edge sets are empty, and `range (N-1)` is empty. S.04 has both sides zero. The matrix bounds already quantify over these cases and have proved nonnegative right sides; no positive-`N` premise is inserted.
- **Empty generic support:** both random subsets are empty under the support hypotheses, and S.03 is zero equals the empty sum. The proof through the existing expected-card theorem includes this case.
- **Empty sample types:** no additional `Nonempty` assumption is added. A supplied normalized finite law on an empty type would itself be inconsistent, and the constructor and identities remain valid for the stated quantified data without manufacturing a sample.
- **`K = 0`:** `hM` forces `M = 0`. The word and tail products are empty, the existing matrix sample space and law remain defined, and the formulas apply to the already defined sorted empty words.
- **`M = 0`:** the prefix is empty, its mass is one, and `prefixMean` is `N`. The whole-deck internal graph is covered without a separate new definition.
- **`M = K`:** the tail factor is the empty product one. Both matrix bounds apply; no tail-randomness premise is required.
- **`k = 0`:** all types and statements remain quantified exactly as written. If columns exist, `hn` forces `N = 0`; if a positive-length prefix is requested there is no map `Fin M → Fin 0`. No inhabitance assumption is silently added.
- **Zero piles and impossible prefixes:** zero entries in `n` are allowed. A zero-mass prefix has zero existing mean, so the already proved matrix bounds imply zero expected overlap. The new addendum does not divide by prefix mass.
- **Zero tail collision factor:** S.05 gives zero expected overlap directly. The proof never divides by that factor.
- **Zero-weight outcomes and null events:** all equalities and subset proofs are finite and pointwise where specified. Neither rectangle probabilities nor intersection counts require a positive event probability.
- **Different laws in S.01–03:** `w` and `v` may differ and their sample types may differ. Only the product construction is shared. The square in S.04 is justified by the explicit specialization to two copies of the same law, not by an implicit identification of arbitrary laws.

The only case distinctions introduced by the new probability proof are finite indicator branches, all proved locally. The existing low-population, zero-factor, and terminal cases in the matrix estimates are inherited without altering their statements. No concentration or stable-block lemma is needed by any declaration in this addendum.

## 7. Independent design conclusion

The six statements are well-typed specializations of the source's exact independent-copy overlap identity in the already implemented finite model. The one new probability construction supplies the required independence instead of accepting the desired intersection formula as a field or premise. I found no mathematical blocker or need for an additional named helper declaration in this inventory. This report awaits comparison with the other independent reports and a new freeze.

## 8. Final comparison and acceptance before freeze

After completing the independent inventory above, I read `overlap_contract_reconstruction.md` and `overlap_contract_assumptions.md` in full. Both reports accept the same constructed product law and the same six propositions. Their semantic theorem descriptions agree with the exact names, argument order, equality directions, and conclusions specified here; neither requests a seventh theorem or a further named helper.

The comparison confirms the following boundaries of the final inventory:

- The product constructor has exactly the two existing finite laws as explicit inputs. It has no `Nonempty` premise, no uniformity premise, and no assumed factorization field.
- The product-expectation theorem retains arbitrary real-valued `f`. The event theorem retains arbitrary coordinate events with locally supplied decisions and includes null events.
- The common element type in S.03 has `[DecidableEq α]` only. There is **no `Fintype α` premise**. Both pointwise support conditions remain exactly as stated; the edge specialization discharges them with the existing support lemma.
- S.04 uses the same law, row map, prefix, population, and absolute edge coordinates in both factors. The product sample has two independent outcomes. It does not identify two copies sharing a random cut array or a conditioning event with this product, and it does not independently recenter the edge sets.
- S.05 and S.06 use the unchanged deterministic matrix data and existing density bounds. Neither adds a positive-population, small-mean, nonterminal-prefix, stable-block, spatial, or asymptotic hypothesis.
- All indicator cases, finite-sum manipulations, support proofs, and square identities fit within local proof steps of the six declarations. **No extra named helper, instance, or definition is needed.** The module layout remains `Overlap/FiniteLaw.lean` and `Overlap/Edges.lean`, with the namespaces specified in section 2.

The assumptions report's recentering example reinforces the fixed-coordinate interpretation already explicit in S.03–04; it requires no change to a proposition. The reconstruction report's source comparisons confirm that the exact overlap identity precedes and does not depend on the unresolved spatial localization bounds. There is no remaining disagreement or hidden-assumption issue in this bounded addendum.

**Final acceptance:** this one-definition, six-theorem inventory is complete and ready to freeze. No Lean code has been written for it, and all earlier freezes and implementations remain unchanged.
