# Independent reconstruction of the shared-edge interpretation

I reread the requested TeX first-moment passage and the corresponding overlap arguments in both permitted PDFs, then checked the proposed finite consequences against the existing `FiniteLaw`, `Deck`, `Density`, and collision-estimate modules. The proposed inventory of one constructed product law and six theorems is mathematically sufficient. No independence premise, new coordinate convention, extra positivity hypothesis, or change to any previous freeze is needed. This is a pre-freeze mathematical report; it contains no Lean implementation.

## Exact source relationship

TeX 460–472 defines shuffle edges at their positions after lexicographic sorting and defines shared edges by intersection. TeX 1837–1841 begins the first-moment proof with the exact identity between the expected number of shared edges and the sum of the squared single-deck edge probabilities. This algebraic identity precedes the profile truncation and localization estimates at 1843–1859; those estimates are not prerequisites for the identity.

The homogeneous paper `2103.05068v3.pdf`, PDF page 7, explicitly distinguishes the identity from the earlier heuristic: its extracted text at lines 352–361 identifies the sum of squared edge probabilities with the expected intersection of two independent graphs. PDF page 18, equation (4.8), applies the same identity to matching prefix blocks (extraction 1002–1008). Lemma 4.11 on PDF page 23 then uses localization and AM–GM to control the total shared-edge expectation by these block contributions. Lemma 5.2 on PDF page 30 reduces expected intersections of independent random subsets to sums of products of their membership probabilities (extraction 1696–1703).

The fixed-column paper `2510.22783v1.pdf`, PDF page 27, proof of Lemma 4.13, writes the exact chain expected shared-edge cardinality = sum of joint edge probabilities = sum of squared edge probabilities before the localization bound (extraction 1619–1623). Its Lemma 5.2 on PDF page 34 states the independent-random-subset comparison inherited from the homogeneous paper (extraction 2070–2075).

Thus this addendum formalizes an exact elementary step common to all three sources. Independence is between the two complete samples. No statement requires different edge locations within one sample to be independent.

## One definition: the actual product law

Define `EdgeLocalization.FiniteLaw.prod` for arbitrary finite types Ω and Λ, existing `w : FiniteLaw Ω` and `v : FiniteLaw Λ`, with result `FiniteLaw (Ω × Λ)`. The exact weight at `(ω,λ)` is `w.weight ω * v.weight λ`.

The constructor proves nonnegativity by multiplication of the two existing nonnegative weights. For normalization, sum first over λ: the inner sum of v's weights is one, and the remaining sum of w's weights is one. Trusted finite product-sum reindexing and distributivity prove this directly. No new normalization condition, binary-independence structure, custom finite instance, or nonempty assumption is added. A finite type with no elements cannot admit an existing normalized `FiniteLaw`; the parameters already enforce that fact without a separate premise.

The constructor is a binary product of possibly different existing laws. In the self-law case, `prod w w` samples two coordinates independently; it is not the diagonal law that sets the second sample equal to the first.

## Complete six-theorem inventory and proofs

The names below describe the proposed roles; the final statement-design report may choose the exact names before freeze. No additional named helper theorem is mathematically necessary.

### 1. Product expectation

For arbitrary finite Ω and Λ, laws w and v, and every `f : Ω × Λ → ℝ`, prove

`(prod w v).expectation f = w.expectation (fun ω => v.expectation (fun λ => f (ω,λ)))`.

There is no sign, integrability, or boundedness hypothesis on f. Expand the frozen finite expectation, turn the product-type sum into nested sums, and rearrange multiplication. The product-space reindexing and scalar distribution are local proof steps. This is the finite Fubini identity for the constructed law, not an assumed distributional property.

### 2. Rectangle-event probability

For `A : Ω → Prop` and `B : Λ → Prop`, prove

`(prod w v).probability (fun z => A z.1 ∧ B z.2) = w.probability A * v.probability B`.

Use theorem 1 with the event indicator. For each ω and λ, split explicitly on Aω and Bλ to prove that the indicator of their conjunction is the product of the two indicators. Finite distributivity or the inner expectation then factors the sums. A null event causes no difficulty: the formula uses multiplication and no event-probability division. The required decidability can remain local classical decidability; no decidability premise on A or B is required in the public statement.

### 3. Expected intersection cardinality

Let α be any type with decidable equality, let `s : Finset α`, and let `H : Ω → Finset α` and `J : Λ → Finset α` satisfy `H ω ⊆ s` for every ω and `J λ ⊆ s` for every λ. Prove

`(prod w v).expectation (fun z => ((H z.1 ∩ J z.2).card : ℝ))`

`= ∑ i ∈ s, w.probability (fun ω => i ∈ H ω) * v.probability (fun λ => i ∈ J λ)`.

No `Fintype α` is needed: s is the common finite support. The support inclusions are the stated hypotheses of this generic counting theorem, and are already proved by F15 when it is applied to deck edges.

The intersection is contained in s, using either support inclusion. Apply existing F12 to the product law and the samplewise intersection. For each i, the event that i belongs to that intersection is exactly the conjunction of its H-membership event on the first coordinate and its J-membership event on the second coordinate. Existing probability congruence and theorem 2 therefore factor the summand. This also covers empty support or an identically empty random set.

### 4. Edge density equals expected same-position overlap

For arbitrary finite Ω, `w : FiniteLaw Ω`, `N : ℕ`, `R : Ω → ℕ → List ℕ`, and arbitrary prefix list x, prove

`edgeDensity w N R x`

`= (prod w w).expectation (fun z => ((internalEdges N (R z.1) x ∩ internalEdges N (R z.2) x).card : ℝ))`.

Specialize theorem 3 with common support `Finset.range (N−1)` and the same edge-set function on each factor. The two support inclusions are exactly the frozen `internalEdges_subset_range`. Every product of matching edge probabilities is its square, and the sum is exactly the frozen `edgeDensity`. Reverse theorem 3's equality to obtain the chosen direction.

The sum is the sum of the squared probabilities at the individual edge locations. It is neither the square of the expected edge count nor the second moment of that count. Those are different quantities; C.47 provides an inequality with the former. The same-index intersection counts edges at identical absolute deck positions. It makes no translation or recentering of either prefix block.

This theorem does not require R to be a sorted deck or a shuffle-generated deck. It is true for the frozen edge-set construction for any R. The actual shuffle interpretation is supplied by the already-defined `sortedRows` when specialized below. Taking x=[] recovers the whole shuffle-graph identity in TeX 1841 without a separate named theorem.

### 5. Actual-matrix overlap bounded by the fourth-power mean-tail expression

Use exactly the existing matrix data: natural N,K,k,M; `n : Fin K → Fin k → ℕ`; the original column-sum proof `hn`; `hM : M≤K`; and `x : Fin M → Fin k`. Let W be the existing `matrixLaw n hn`. Prove

`(prod W W).expectation (fun z =>`

`  ((internalEdges N (sortedRows n z.1) (prefixWord x) ∩`

`    internalEdges N (sortedRows n z.2) (prefixWord x)).card : ℝ))`

`≤ (prefixMean N n hM x)^4 * (tailCollisionFactor N n M)^2 / 4`.

Theorem 4 rewrites the left side as the existing matrix edge density. Apply the already-proved `matrix_internal_density_le_mean_tail_fourth` (C.54). All parameters and the coefficient 1/4 remain unchanged. There is no new two-deck collision calculation or denominator manipulation.

### 6. Actual-matrix overlap bounded by the prefix mean

For exactly the same data and left-hand expectation as theorem 5, prove

`expected overlap ≤ prefixMean N n hM x`.

Again use theorem 4 and the already-proved `matrix_internal_density_le_prefixMean` (C.55). No small-mean, terminal-prefix, or positive-pile premise is required. The result includes the terminal case M=K while retaining its valid broader finite domain.

## Cases and possible hidden assumptions

* **N=0 or N=1:** the common support is literally `range (N−1)` with natural subtraction, hence empty. Both internal-edge sets, their intersection, and the density vanish. The actual-matrix bounds already include these sizes, so no N≥2 assumption is introduced.
* **Empty support s:** both generic random sets are empty by the support hypotheses and the sum is empty. No selected support element is needed in the proof.
* **Deterministic laws or deterministic decks:** probabilities are zero or one and the equality remains exact. Nonuniform laws and zero-weight atoms are also permitted by the existing law structure.
* **Empty sample type:** the existence of an existing normalized law would be contradictory. No constructor proof chooses an element, and no extra nonempty typeclass is necessary.
* **Zero-probability rectangle or membership event:** its factored probability is zero. Neither Fubini nor the intersection identity divides by a probability.
* **K=0:** M=0, all row words are empty, and each graph has N−1 deterministic edges. The product overlap and density both equal N−1. The core bounds remain valid with prefix mean N and empty tail factor one.
* **M=0 or M=K:** the prefix or suffix products retain their existing empty-product values. The product law does not resample a reduced block or change the column population.
* **k=0:** with a column present the existing sum proof forces N=0; with no columns arbitrary N remains permitted. No new alphabet element is chosen.
* **Zero selected prefix pile, a selected pile of size one, or a zero tail coincidence factor:** existing matrix density results cover these cases. In particular, the relevant edge overlap is zero when the corresponding core density is zero. There is no positivity restriction on these factors.
* **Different word occurrences and sorting ties:** the pair consists of two independent full matrix samples, each sorted by its existing sample-dependent sorting map. Their edge sets are compared at the same original deck positions. Neither sorting map is required to be independent of its own matrix, and no equality of the two sorting permutations is assumed.
* **Dependence across edge positions:** allowed. Only a first-moment sum over edge indicators is used. No product over different i and no joint law of the edge indicators within one deck enters the proof.
* **Conditioning or mixtures:** the abstract theorem applies to any given finite law w through its constructed self-product. It does not identify a common-exploration-conditioned pair, two samples sharing random cuts, or any other coupled pair with that self-product. The actual-matrix corollaries use deterministic n and its existing law. Further conditional/random-pile interpretations need their own reviewed statements.

## Dependencies and acceptance

The definition's constructor uses the frozen law structure and trusted finite-sum facts. Theorems 1 and 2 establish product expectation and rectangle factorization. Theorem 3 combines theorem 2 with F12. Theorem 4 specializes theorem 3 using F15 and the frozen density definition. Theorems 5 and 6 combine theorem 4 with C.54 and C.55 respectively. This is an acyclic inventory of exactly six new named propositions. All indicator algebra, support checks, and product normalization steps can remain local proofs.

I accept the proposed one-definition/six-theorem scope. The common-support hypotheses belong only to the generic intersection theorem, and are discharged by proved project lemmas in the deck application; they are not new shuffle assumptions. The resulting theorems make the user's requested interpretation an actual finite Lean target. They do not by themselves prove the stable-block summation, the global negative-power first moment, or the exponential-moment and exploration steps, all of which remain outside this bounded addendum.

## Final-signature comparison and acceptance

I have compared the complete `overlap_contract_statements.md` and `overlap_contract_assumptions.md` with this independent reconstruction. I accept S.D01 and S.01–S.06 exactly as specified, with no remaining pre-freeze issue. The product constructor's literal multiplicative weight and derived normalization, the arbitrary signed-function Fubini statement, the rectangle probability statement, and the intersection theorem's common finite support and decidable equality have the intended semantics. Both sample laws and their types may differ in S.01–S.03; α requires no Fintype or nonempty assumption. The support premises remain pointwise rather than almost-sure premises.

S.04 uses the same law, row map, N, prefix, and absolute edge-coordinate system for its two independent samples. Its equality direction agrees with the frozen density definition and the exact expected-intersection interpretation. S.05–S.06 retain precisely the existing feasible matrix data and all-size coefficients from C.54/C.55. The case and recentering audit agrees with the reconstruction, including null events, empty supports, N=0/1, zero piles and factors, and the distinction between the product law and a diagonal or conditioned coupling.

The proposed two-module allocation is acyclic: `Overlap/FiniteLaw.lean` contains only the single definition S.D01 and S.01–S.03, and `Overlap/Edges.lean` contains only S.04–S.06 using that module and the proved collision estimates. No additional named helper, new custom instance, conditional-copy hypothesis, or change to any earlier frozen item is required. No Lean implementation has been authored for this addendum before the new freeze.
