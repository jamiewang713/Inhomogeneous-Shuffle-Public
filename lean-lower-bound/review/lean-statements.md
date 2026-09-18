# Independent Lean-statement review

Reviewer: Lean-statement design agent. Mathematical sources read: the supplied unified TeX article, and the supplied PDFs `2103.05068v3.pdf` and `2510.22783v1.pdf` through their local text extractions. No other mathematical source was used. This is a proposed contract for review, not a claim that the results below have been formalized.

## Representation and exact probability convention

Use namespace `RiffleLower`. On a finite type `α`, `FiniteLaw α` has real-valued mass, pointwise nonnegativity, and total mass one. For a finite event `A`, `prob P A = ∑ a ∈ A, P.mass a`. Set `expect P f = ∑ a, P.mass a * f a`, `variance P f = expect P (fun a => (f a - expect P f)^2)`, and `TV P Q = (∑ a, |P.mass a - Q.mass a|) / 2`. On a nonempty finite type, `uniformLaw` has mass `(Fintype.card α : ℝ)⁻¹`. These conventions were agreed with the root agent before this proposal.

All finite deck indices are zero-based. A permutation maps output positions to original card labels. A **contiguous increasing run** of length `m` means there is a start `a` with `a + m ≤ N`, such that the restriction `j ↦ σ (a + j)` on `Fin m` is strictly increasing. It does not mean an arbitrary subsequence. The defining event depends only on the observed permutation and on `N,m`.

The concrete fixed-column model needs no probabilistic independence assumptions in theorem arguments. Fix natural numbers `N,K,k` and deterministic columns

`c : Fin K → Fin N → Fin k`.

Let `Ω := Fin K → Equiv.Perm (Fin N)` and put the uniform law on `Ω`. The coordinate permutations are thereby independent and uniform by construction. Define

* `rowWord c ω i : Fin K → Fin k` by `t ↦ c t (ω t i)`;
* `columnCount c t a := #{i : Fin N | c t i = a}`;
* `wordCount c w ω := #{i : Fin N | rowWord c ω i = w}`;
* `wordMass c w := ∏ t, (columnCount c t (w t) : ℝ) / N`;
* `wordMean c w := (N : ℝ) * wordMass c w`;
* `pairWordMass c w := ∏ t, ((columnCount c t (w t) : ℝ) * (columnCount c t (w t) - 1)) / ((N : ℝ) * (N - 1))`.

The last definition uses subtraction in `ℝ` after casting; the corresponding natural falling factorial is `d*(d-1)`. These agree for natural `d` including `d=0`.

Permuting a deterministic column is exactly uniform over assignments with its multiplicities: every assignment with the same counts has exactly `∏ a, (columnCount c t a)!` preimages. This identification is mathematically valid. The finite lower-bound theorem can use the concrete permutation-of-columns model directly and does not need to assert this identification as an unproved interface theorem. If identification with a separately defined shuffle process is included, it must be proved.

## Proposed exact moment module: definitions and all mathematical helpers

This module should export only the following definitions/results. Additional local proof steps can be private lemmas with statements implied by this list, but no new model hypothesis or probability axiom may be introduced.

1. **`columnCount_le`**. For every `c,t,a`, `columnCount c t a ≤ N`.

2. **`sum_columnCount`**. For every `c,t`, `∑ a, columnCount c t a = N`.

3. **`wordMass_nonneg` and `wordMass_le_one`**. For `0 < N`, `0 ≤ wordMass c w ≤ 1`. Consequently `0 ≤ wordMean c w ≤ N`.

4. **`uniform_expect_equiv`**. For finite nonempty `α,β`, an equivalence `e : α ≃ β`, and `f : β → ℝ`, `expect (uniformLaw α) (fun a => f (e a)) = expect (uniformLaw β) f`. This is a finite change of variables and belongs in the common finite-law module if already proved there.

5. **`uniform_pi_expect_prod`**. For a finite coordinate type `T`, finite nonempty coordinate types `A t`, and `f : ∀ t, A t → ℝ`,

   `expect (uniformLaw (∀ t, A t)) (fun ω => ∏ t, f t (ω t)) = ∏ t, expect (uniformLaw (A t)) (f t)`.

   This is the precise independence statement needed. It must be proved by finite sum/product expansion, with no supplied independence hypothesis.

6. **`exists_perm_map_pair`**. For a finite type with decidable equality and `i ≠ j`, `i' ≠ j'`, there exists `ρ : Equiv.Perm α` with `ρ i = i'` and `ρ j = j'`. Two explicit transpositions suffice. This is only a symmetry helper; an existing trusted mathlib theorem can replace it.

7. **`uniform_perm_one_indicator`**. For `0 < N`, a subset `S : Finset (Fin N)`, and `i : Fin N`,

   `expect (uniformLaw (Equiv.Perm (Fin N))) (fun σ => if σ i ∈ S then 1 else 0) = (S.card : ℝ) / N`.

   Prove exchangeability under composition and double count the successes over `i`. Do not postulate evaluation uniformity.

8. **`uniform_perm_two_indicators`**. For `2 ≤ N`, `S : Finset (Fin N)`, and distinct `i,j : Fin N`,

   `expect (uniformLaw (Equiv.Perm (Fin N))) (fun σ => (if σ i ∈ S then 1 else 0) * (if σ j ∈ S then 1 else 0)) = ((S.card : ℝ) * (S.card - 1)) / ((N : ℝ) * (N - 1))`.

   Use pair transitivity and count ordered distinct selected positions. This is sampling without replacement, not independence of rows.

9. **`word_row_probability`**. For `0 < N` and `i : Fin N`,

   `prob (uniformLaw Ω) {ω | rowWord c ω i = w} = wordMass c w`.

   Here and below displayed predicate events stand for `Finset.univ.filter` with that predicate.

10. **`word_two_rows_probability`**. For `2 ≤ N` and distinct `i,j : Fin N`,

   `prob (uniformLaw Ω) {ω | rowWord c ω i = w ∧ rowWord c ω j = w} = pairWordMass c w`.

11. **`wordCount_expect`**. For `0 < N`,

   `expect (uniformLaw Ω) (fun ω => (wordCount c w ω : ℝ)) = wordMean c w`.

12. **`wordCount_factorial_second_moment`**. For `2 ≤ N`,

   `expect (uniformLaw Ω) (fun ω => (wordCount c w ω : ℝ) * (wordCount c w ω - 1)) = (N : ℝ) * (N - 1) * pairWordMass c w`.

13. **`one_column_pair_le_square`**. For natural `d,N` with `2 ≤ N` and `d ≤ N`,

   `(d : ℝ) * (d - 1) / ((N : ℝ) * (N - 1)) ≤ ((d : ℝ) / N)^2`.

   The left side is nonnegative. The estimate is valid also for `d=0,1`; these must not be excluded to simplify a proof.

14. **`pairWordMass_le_square`**. For `2 ≤ N`, `pairWordMass c w ≤ (wordMass c w)^2`.

15. **`wordCount_variance_le_mean`**. For `2 ≤ N`,

   `variance (uniformLaw Ω) (fun ω => (wordCount c w ω : ℝ)) ≤ wordMean c w`.

   In fact the factorial moment is at most `N(N-1) λ² ≤ N² λ²`; expanding the variance gives the result. No strict positivity of pile counts, support condition, or bound on `K` is needed.

16. **`finite_lower_tail`**. For any finite law `P`, real-valued `Y`, `μ = expect P Y`, and real `b < μ`,

   `prob P {ω | Y ω < b} ≤ variance P Y / (μ - b)^2`.

   This follows directly by bounding the indicator by the centered square divided by `(μ-b)^2`; it requires no nonnegativity of `Y`.

17. **`wordCount_lower_tail`**. For `2 ≤ N`, natural `m`, and `(m : ℝ) < wordMean c w`,

   `prob (uniformLaw Ω) {ω | wordCount c w ω < m} ≤ wordMean c w / (wordMean c w - m)^2`.

   Equivalently, the success probability of `{ω | m ≤ wordCount c w ω}` is at least one minus that quantity. The value can exceed one, which merely makes the estimate trivial; no condition such as `μ ≥ 2m` is necessary.

## Proposed concrete finite lower bound

Give `Word := Fin K → Fin k` its **lexicographic** linear order, not the usual pointwise partial order. Let `inverseShuffle c ω := Tuple.sort (rowWord c ω)` and `shuffleLaw c` be the pushforward of `uniformLaw Ω` by `inverseShuffle c`.

For `N ≥ 2`, `1 ≤ m ≤ N`, and `(m : ℝ) < μ := wordMean c w`, the exact intended theorem is

`1 - μ / (μ - m)^2 - (N : ℝ) / (Nat.factorial m : ℝ) ≤ TV (shuffleLaw c) (uniformLaw (Equiv.Perm (Fin N)))`.

Proof dependencies are the proved moment bound, stable-sort full-word run lemma, uniform increasing-run estimate, and finite hypothesis-test TV inequality. The target word `w` is arbitrary; a coordinatewise maximizing word gives the largest-pile specialization without changing any assumptions.

This is a meaningful finite theorem for every deterministic time-dependent column sequence. It imposes no homogeneous cutoff, time-profile integral, regularity, bounded-away-from-zero, local-good-column, or asymptotic assumptions. Its assumptions must be frozen exactly before implementation.

## Other finite interfaces reviewed

### Stable sorting and cold edges

`Tuple.sort` already implements stable sorting. Trusted mathlib `Tuple.eq_sort_iff` proves both monotonicity of sorted values and the tie rule `i < j → f (sort f i) = f (sort f j) → sort f i < sort f j`. The equal-value fiber of a monotone tuple is an interval. Thus every full-word fiber is a contiguous increasing run of exactly its occupancy size. A shorter prefix fiber need not be increasing across distinct full words.

For a monotone sorted-word tuple `s`, selected words `W`, and a finite set of positions `H`, define equality edges using adjacent positions both belonging to `H`. If every occurrence of each `w ∈ W` is in `H`, then

`#{w ∈ W | occupancy s w ≥ 2} ≤ #{i | i,i+1 ∈ H ∧ s i = s (i+1)}`.

The proof picks the first occurrence of each duplicate word; monotonicity makes the next position equal, and distinct words select distinct edges. Stable ties turn these equality edges into ascent edges of the observed inverse permutation. This is the valid deterministic core of cold localization/collision counting. It alone does not give an excess over the uniform ascent mean.

### Time-dependent profiles

For a finite cell map `cell : Fin K → C`, define `profile w q a` to be the number of times `t` with `cell t=q` and `w t=a`. Exact mass factorization by a profile requires the explicit equality `p t a = representative (cell t) a`. Under that condition,

`∏ t, p t (w t) = ∏ q, ∏ a, representative q a ^ profile w q a`.

Without exact equality, use coordinatewise lower/upper envelopes and a proved product inequality. Do not assert that a global count of digit frequencies determines word mass under arbitrary time dependence. A second exact inhomogeneous identity is

`∑ w, (∏ t, p t (w t))^r = ∏ t, ∑ a, (p t a)^r`

for a natural `r` (in particular `r=2,3,4`). A coordinatewise maximum word realizes `∏ t max_a p t a`. These statements justify finite costs; they do not justify replacement of homogeneous constants by integrals.

### Uniform permutations and ascents

For any injective list of `m` positions, the probability that their values appear in increasing relative order under a uniform permutation is `1/m!`. A union bound over the at most `N` admissible starts gives `N/m!` for a contiguous run. Exact hypotheses are `m ≤ N` and injectivity of the selected positions; `m=0` is a valid relative-order formula, though the lower-bound application uses `m≥1`.

For any finite path-edge set `E`, the ascent count has mean `|E|/2`. Distinct disjoint edges have joint ascent probability `1/4`, while adjacent edges have joint ascent probability `1/6`; hence

`Var(A_E) = |E|/4 - adjacentPairs(E)/6 ≤ |E|/4`.

Pairwise independence does not itself establish joint independence of all odd edges; the latter has its own proof by independent swaps of the disjoint endpoint pairs. A second-moment tail is a useful finite estimate, but does not suffice for union over exponentially many environment-dependent cold tests.

### Random pile environments and common observable events

For a finite environment law `η`, laws `P_e`, and a single fixed event `A`, the mixture has event probability `∑e η(e) P_e(A)`. Therefore any bounds `P_e(A) ≥ 1-ε_e` imply

`TV (mixture η P) U ≥ 1 - ∑e η(e) ε_e - U(A)`.

The increasing-run event has exactly this common-event property even when the largest word and its mass depend on the environment. For a typical subset `G` and uniform error `ε` there, one obtains `TV ≥ η(G)(1-ε)-U(A)`; the proof may discard atypical environments using their nonnegative contribution.

For different events `A_e`, use `A := ⋃e∈G A_e`, which remains an observable event on permutations, and prove

`TV (mixture η P) U ≥ ∑e∈G η(e) P_e(A_e) - ∑e∈G U(A_e)`.

No inference from large conditional TV to large mixture TV is valid without such a common test or union test. The finite union penalty must remain explicit unless a proved false-positive tail beats the number of tests.

## Gaps that exclude the full asymptotic cold theorem from this contract

1. The TeX's `block-bd` lemma is false as stated. With an empty reservoir and all relevant block value sets but one fixed, the last block is determined. The stated one-coordinate oscillations may therefore all be zero while the function of the random partition is nonconstant. Its claimed Doob increment bound does not follow. Consequently `permutation-bd` and the later Lalley comparison are not available without a corrected independent proof.

2. The component comparison proof says clipped intersections have total contribution `O(|∂H|)`. A clipped component can contain arbitrarily many internal edges. One may be able to retain their favorable internal contributions while discarding only boundary comparisons, but that is a different argument and must be supplied explicitly.

3. The old homogeneous PDF `2510.22783v1` writes the largest-pile threshold `K ≤ (tilde C_μ - ε) log N` in cold-test Lemmas 6.3 and 6.5 although the section has imposed `K ≥ (tilde C_μ + ε) log N`. These copied thresholds should not enter any finite criterion. The genuine finite ascent-test mechanism is time-free.

4. Source occupancy indicators are negatively correlated in the independent-row model of `2103.05068v3`. They cannot be transported to fixed-count columns merely by quoting that proof: different words can be positively correlated. The target-word row indicators needed by the largest-pile argument do have a directly provable pair bound, as frozen above.

5. Time-inhomogeneous cold witness selection, bridge reservation, uniform relative endpoint control, rounded/truncated cellwise types, and central-window joint occupancies require new estimates with explicit scales. A conditional wrapper that assumes their desired conclusion is not a formalization of those estimates.

6. The random-pile extension requires a common permutation event and uniform conditional errors. Polynomial Chebyshev control cannot absorb `exp(O(log²N))` environment tests. The largest-run core avoids that penalty because its test is common to every environment.

## Trusted mathlib APIs inspected

* `Mathlib/Data/Fin/Tuple/Sort.lean`: `Tuple.sort`, `Tuple.monotone_sort`, `Tuple.eq_sort_iff`, `Tuple.eq_sort_iff'`, `Tuple.graphEquiv₂`.
* `Mathlib/Data/Fintype/Perm.lean`: `Fintype.card_perm`.
* `Mathlib/Algebra/BigOperators/Ring/Finset.lean`: `Finset.prod_univ_sum`, `Finset.sum_prod_piFinset`, `Fintype.prod_sum`, `Fintype.sum_mul_sum`.
* Finite equivariance can be proved using `Equiv.sum_comp` / finite sum reindexing; exact available theorem signatures should be checked before use.

No Lean source has been written by this review agent before statement freeze.
