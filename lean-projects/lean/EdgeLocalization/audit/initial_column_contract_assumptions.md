# Independent pre-code audit: first-column separation

This audit rereads only the permitted mathematical sources and existing proved project definitions. No Lean implementation or new freeze is proposed by this report, and no earlier contract, review, source, or implementation is changed. I completed this independent audit before comparing the other reviewers' reports.

## Source meaning

The TeX defines the law as independent uniform fixed-histogram columns, followed by lexicographic row sorting (390–395 and 448–452). Its internal graph joins equal adjacent full rows, and a prefix subgraph retains those edges whose endpoint rows have that prefix (460–472). It defines samplewise ambient recentering at 509–511 and identifies the first moment with the sum of squared absolute edge probabilities at 1837–1841.

The fixed-column paper 2510.22783v1 explicitly separates first-digit pieces because the number of rows with each first digit is deterministic: see the introduction on PDF page 6, §3.2 on pages 14–15, and the observation immediately before Definition 3.8 that different first-digit pieces occupy disjoint intervals independent of the graph. This is the exact feature that justifies matching the same pieces across two independent samples.

That paper's Definition 4.3 and the formulas on page 19 deliberately start the left and right fluctuation maxima at column 2. The first-column contribution to the lower endpoint is a deterministic cumulative pile count; it is not a source of fluctuation. Lemma 4.5's proof then sets N′ to the selected first-column pile count and uses the separate good-first-shuffle fact N′ ≤ (1−χ)N on page 20. Both conventions matter: excluding deterministic first-column motion does not itself prove the quantitative complement bound.

The older homogeneous multinomial paper 2103.05068v3 has independent random digits and hence random first-digit pile counts; see §2.2 on PDF pages 8–9 and the mixture/overlap argument in §3.1. Its deterministic interval parameters in [0,1) describe probability masses, not deterministic occupied intervals in the sorted deck. Therefore the exact fixed-count separation below must not be transferred to that unconditional model merely because both models use lexicographic sorting.

## Exact finite separation is valid

Assume K ≥ 1 and use the actual first column j₀ = 0 in zero-based Lean coordinates. For each digit a, write qₐ = n(j₀)(a) and

`cₐ = ∑ b with b < a, n(j₀)(b)`.

For every outcome of the fixed-histogram matrix, the sorted first-digit cylinder [a] has exactly qₐ occupied positions and its zero-based left cut is cₐ. Its occupied positions are exactly the natural interval `[cₐ, cₐ + qₐ)`. These facts are deterministic consequences of the column histogram and the proved sorting permutation and monotonicity. They do not require uniform probability, independent rows, good columns, positivity of qₐ, or conditioning. The probability theorem may use the actual `matrixLaw` as requested; the geometric inputs need no additional feasibility premise beyond what a given `FixedMatrix` outcome already contains.

Every empty-prefix internal edge has equal full endpoint rows. Because K ≥ 1, those rows have the same well-defined first digit. Thus the absolute edge set partitions into first-digit internal edge sets. More strongly, its digit at a given absolute edge position is the same in every outcome in which that edge is present, because the first-digit occupied intervals are deterministic. This stronger assertion eliminates cross terms when probabilities are squared. Disjointness of the digit events within a single outcome alone would not suffice.

Translation by cₐ gives a bijection between the absolute internal edges in cylinder [a] and its existing relative internal edges shifted by `ambientLeft ... [a]`. Both independent samples use the identical deterministic cₐ. Their translated intersection therefore has the same cardinality as their absolute intersection within that digit. Consequently, pointwise for two matrix outcomes, the number of shared whole-deck edges is the sum of these relative within-digit intersection cardinalities. Taking expectation under the already constructed independent product law and applying the proved overlap identities yields exactly

`global absolute edge density at [] = ∑ a, relative edge density at [a], shifted by its own ambientLeft`.

There is no loss, inequality, extra error, or independence assumption between the different digit pieces. Those pieces can be dependent because every tail column has fixed total counts. The proof uses only the two independent full matrix samples already encoded by the product law and linearity over their finite overlap partition.

Equivalently, one may prove the identity directly by first partitioning the deterministic absolute support and then translating each summand. Either route must establish the deterministic supports; applying a general random-shift density equality would be invalid.

## Coordinate and support details

The Lean edge index i represents the paper's edge (m,m+1) with m = i+1. Thus the first-digit cut is cₐ, whereas its one-based lower endpoint in the paper is cₐ+1. The existing shift is exactly cₐ, not cₐ+1.

For an internal edge at absolute index i in digit a, the clean endpoint condition is `cₐ ≤ i` and `i+1 < cₐ+qₐ`. Its relative index is i−cₐ and satisfies `i−cₐ+1 < qₐ`; in particular the relative edge support is contained in `range (qₐ−1)`. This formulation avoids incorrect arithmetic with a zero pile and natural subtraction. All results also remain valid using the already frozen common support `range (N−1)`.

Relative edges belonging to different digits need not have disjoint relative indices: many pieces may have an edge at relative index zero. The requested right-hand side is a sum of their separate squared densities, not the squared density of a union of their recentered sets. Their absolute supports, which are disjoint before translation, are what justify this sum.

The `ambientLeft` definition filters positions in `range N`. Its row adapter outside that range returns the empty list, which is lexicographically below a nonempty one-digit prefix; these artificial rows must never enter a count or a first-digit assertion. Use valid row labels or prove i<N from membership before evaluating a head digit. Ties in full rows do not affect the first-digit interval: every sorting permutation orders the same histogram into the same digit sequence.

The one-digit prefix should be the existing list `[a.val]` or the existing `prefixWord (fun _ : Fin 1 => a)`, with their equality proved locally if both forms occur. No new legality assumption is appropriate: zero-count digits are required terms of the finite sum and contribute zero automatically.

## Exceptional finite domains

- **K=0:** every full row is the empty word. The internal graph for prefix [] is the deterministic complete N-vertex path, with `range (N−1)` as its edge-index set and squared edge density `(N−1 : ℕ)` cast to ℝ. A separate theorem must state this exact case. There is no first digit, and a sum of one-digit densities is zero, so the proposed separation would be false without the K ≥ 1 domain whenever N ≥ 2.
- **N=0 or N=1:** the edge support is empty and every relevant density and overlap count is zero. The K=0 formula uses truncated natural subtraction and gives zero in both cases. The K ≥ 1 separation is also zero on both sides without choosing a nonexistent valid edge index.
- **Empty or singleton piles:** qₐ=0 or qₐ=1 gives no internal edge in that piece. Consecutive zero piles may have equal cumulative cuts, and a trailing zero pile may have cut N. No proof may assume strict growth of all cuts, a nonempty cylinder, or an internal edge in every digit.
- **A column with one pile of size N:** the identity still holds. Its one nonempty first-digit piece is the whole deck, so the decomposition provides no proper smaller ambient or complement.
- **Empty alphabet:** when K ≥ 1 and N>0, the feasibility equation itself rules out such data. When N=0 the empty-alphabet sum and edge density are both zero. When K=0, an empty alphabet is possible for every N, and the deterministic empty-word path formula still applies.
- **K=1:** each first-digit cylinder consists of identical one-letter rows and is a deterministic path of length `qₐ−1`. The identity reduces to the exact count `∑ₐ (qₐ−1)` in ℕ, cast to ℝ. The boundary between two nonempty different digits is absent even if the two piles are consecutive.

These cases need explicit treatment in statements or local proof branches, not an implicit restriction to large N or positive pile sizes.

## Why deterministic cuts are essential

For a concrete contrasting model, take N=2, K=1 and two independent fair binary row digits, so first-column counts are random. The global edge is present with probability 1/2 and hence has squared density 1/4. Each first-digit relative edge is present with probability 1/4, so summing the two relative squared densities gives only 1/8. The missing contribution comes from one sample having two zeroes and the other having two ones: they share the same absolute edge but not a first-digit class. Fixed column counts exclude exactly this mismatch.

The same warning applies to random-pile mixtures: conditional on one common realized deterministic pile sequence, the exact fixed-count identity holds. Two independent samples from the unconditional mixture can have different first cuts. No unconditional equality follows by averaging the conditional equality or by silently sharing the sampled counts between the two copies. That would change the coupling and the meaning of the squared mixture probabilities.

No analogous deterministic-cut assertion is available for arbitrary deeper prefix cylinders, whose occupancies and left endpoints can fluctuate even with every column histogram fixed. The present first-column statement must not be used as a general samplewise translation invariance of squared density.

## What properness can and cannot be derived

Feasibility gives qₐ ≤ N and N−qₐ equal to the sum of the other pile counts. Strict properness qₐ<N follows exactly when some other pile has a positive count. This is a valid derived finite criterion, but it is not an unconditional consequence of the separation. Even two positive piles need not provide a fixed-fraction complement: `(N−1,1)` has only a complement of size one for its largest piece.

The current TeX definition of a χ-good column has at least two coordinates at least χ. For N>0 and χ>0, if that property is independently available for the actual first column, then for each a one can choose a different one of these two coordinates. Its mass at least χ gives qₐ≤(1−χ)N. Every descendant of [a] then has realized occupancy at most qₐ and so leaves at least χN outside rows. This bound uses the original population N; it does not identify the law inside the piece with a new independent fixed-count law on qₐ rows.

The fixed-column paper's formal definition of χ-good is outside the χ-neighborhoods of simplex vertices, which directly implies its displayed maximal-pile bound. For k>2 this definition is not literally equivalent at the same χ to the current TeX's two-coordinates-at-least-χ definition. Both give the useful complement bound in their respective settings, but a future theorem should use the actual selected definition and prove its implication rather than treat these conventions as identical.

The old initial-shuffle reduction is separate mathematics. In 2510 §3.1, Lemma 3.1 uses total-variation contraction under convolution to discard initial shuffles; Lemma 3.2 locates good shuffles and its offset convention preserves the homogeneous almost-like property after the shift. The resulting shortened process has a good first shuffle. This is not an identity of the original and shortened graph densities, nor an assertion that the original first column was good.

The TeX's local-good condition at 307–316 guarantees a supply of good columns in macroscopic intervals, not goodness of column 1. Transferring an initial-column deletion through a time-dependent profile, local-good condition, and the upper-bound margins still needs a proved argument. The exact separation alone supplies none of those transfers. It also does not guarantee that the individual first-digit means have a limiting size exponent, satisfy the required ambient margins, or satisfy those margins uniformly across a growing family.

The most charitable connection to the intended spatial argument is therefore precise but conditional on future proved reductions: first separate the deterministic first-digit pieces, exclude column 1 from fluctuation computations as the old proof does, and establish an actual quantitative outside-row supply before applying any smoothing argument. This does not validate the presently printed root fluctuation bound. The earlier spatial counterexample and frozen obstruction remain unchanged.

## Minimal finite proof obligations to compare with the statement designer

The decomposition needs the following exact content, without adding concentration or a good-column premise:

1. A deterministic first-column cut, expressed by cumulative counts, together with equality to the existing `ambientLeft` for a one-digit prefix. A new definition is optional if the sum is written explicitly.
2. Exact sorted first-digit membership in its cumulative interval, or equivalent occupancy and ordering facts strong enough to prove common deterministic supports. Its proof must derive the histogram preservation from the existing sorting permutation; it must not assume the interval property.
3. A complete partition of absolute shared edges by digit for two arbitrary matrix outcomes, plus preservation of each within-digit intersection under the common first-digit shift. These may be combined into one pointwise cardinal identity if all local bridges are proved inside it.
4. The requested squared-density equality under the actual `matrixLaw`, using existing finite expectation/overlap identities. No extra independence of pieces or conditional-law interface is needed.
5. The exact K=0 empty-word graph and density result, so the no-first-column case is explicit.

A relative-support lemma for `range (qₐ−1)` is useful if the implementation needs it, but its mathematical claim already follows from item 2 and the existing relative-edge definition. A pure count-complement criterion can be designed later if an actual downstream theorem needs it; no quantitative complement should be made a premise of the unconditional separation result. These are pre-code logical obligations, not permission to add unfrozen helper declarations during implementation.

**Independent verdict:** the proposed exact first-column density separation is true on its stated K ≥ 1 fixed-count domain, with a separate deterministic K=0 formula. It is a useful source-coordinate bridge and a prerequisite for the old first-digit exploration organization. It does not by itself repair the root spatial lemma, derive a good initial column, prove a quantitative proper-ambient condition, or authorize a new conditioning model. Final exact signatures still require comparison before a separate freeze.
