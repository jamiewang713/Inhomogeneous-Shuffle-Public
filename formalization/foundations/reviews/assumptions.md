# Independent adversarial review of the finite foundations

This review was reconstructed independently from only the three authorized mathematical sources. No other project proof notes or agents' reports were consulted, and no Lean statements or proofs have been written by this reviewer.

## Source locations

- `time_inhomogeneous_riffle_shuffle_unified_article.tex`, lines 87–102: `k ≥ 2`, deterministic nonnegative integral pile counts summing to `N`, normalization `p = n/N`.
- TeX lines 388–408: uniformly sampled fixed-column-count matrices, sorted rows, graph edges joining identical adjacent full rows, graph representation.
- TeX lines 445–470: legal words, depth at most `K`, legal prefix tree, cylinders, parent of a non-root word, prefix-induced edge sets.
- TeX lines 788–827: stable partitions use uniqueness along a root-to-leaf path, antichains, disjoint cylinders, and their lexicographic contiguity.
- TeX lines 2915–2958: full-row strings, finite product weights, deterministic half-open intervals, realized prefix blocks and proposed endpoints.
- TeX lines 2961–3007: labelled rows remain labelled during thinning; sorting enters only to identify their resulting contiguous block.
- `2103.05068v3.pdf`, printed/PDF pages 5–6, Proposition 2.1 and Proposition 2.2: shuffle composition, lexicographic order (including the shorter-word convention), sorted row strings, and shuffle graphs.
- `2103.05068v3.pdf`, pages 8–9, (2.1)–(2.3): product weights and half-open deterministic cylinder intervals, with the fixed-depth partition of `[0,1)`.
- `2103.05068v3.pdf`, page 16, Section 4.1.1: prefix cylinders, correct count endpoints, empty-block convention, and induced graph.
- `2103.05068v3.pdf`, pages 32–33, Lemma 5.5: decomposition of a lexicographic interval into a bounded number of prefix cylinders.
- `2510.22783v1.pdf`, pages 7–8, Section 2.2 and Proposition 2.2: fixed-count matrices, uniform raw-matrix law, chronological columns and the append-a-column induction.
- `2510.22783v1.pdf`, page 11, (2.13)–(2.17): prefix cylinders and endpoints. Formula (2.15) has an off-by-one inconsistency discussed below.

## Conclusions that matter before freezing

### Normalization and support

1. Normalization requires `0 < N`. With `N = 0`, Lean's totalized division gives every normalized count zero, so their sum is zero, not one. This is a necessary frozen assumption whenever proving the profile sums to one. Counts should be natural numbers, so nonnegativity is structural rather than an extra hypothesis.
2. Zero piles are explicitly allowed in the inhomogeneous model. Do not silently freeze strict positivity of every coordinate. A legal letter uses a strictly positive count at its actual time coordinate.
3. The source assumes `k ≥ 2`, but the finite foundations remain valid at `k = 1`. A single normalized profile with `k = 0` and `N > 0` cannot exist. If profiles are indexed only by `Fin K`, the combined case `K = 0, k = 0` still has the empty word and no actual columns, so it must not be accidentally ruled out or claimed impossible unless `k ≥ 2` is deliberately frozen globally.
4. `K = 0` is mathematically coherent: the root is the only full word, its product weight is one, its deterministic interval is `[0,1)`, all rows coincide, and the shuffle graph is the entire path. There is no reason to add `0 < K` for these elementary results.
5. Existence of a positive pile at each actual column follows from the count sum and `N > 0`. This yields extensions of every legal prefix to a legal full word. It must be proved, not assumed independently.

### Prefixes, trees, and cylinders

6. Legality must include the depth bound `length ≤ K`; otherwise it is undefined, or a totalized out-of-range lookup can create artificial legal words.
7. A prefix of a legal word is legal. The root is legal. Prefixes of one word are comparable by prefix order, even though arbitrary legal words are not.
8. A non-root word has a unique immediate parent, obtained by dropping its final digit. A child must increase the depth by exactly one. At a terminal word there are no children. Consequently the identity “a cylinder is the union of its children's cylinders” needs `length < K`. At `length = K` the left-hand side is a singleton and the right-hand side is empty.
9. The abstract legal cylinder of every legal prefix is nonempty. A realized matrix block can nevertheless be empty. Example: `N = 2`, `K = 2`, both column counts `(1,1)`, and rows `01,10`. Word `00` is legal, but no row has this prefix.
10. Distinct comparable legal prefixes can have exactly the same legal cylinder. Example: every pile profile is `(N,0)`, so the root, `0`, and `00` all have the same full-word cylinder (where their depths are allowed). Thus cylinder equality does not imply prefix equality, strict extension need not strictly shrink a cylinder, and cylinder inclusion alone does not characterize prefix order. These failures are already present with the source's `k = 2`; they do not depend on allowing `k = 1`.
11. Two legal cylinders intersect if and only if their prefixes are comparable. The forward direction is a fact about prefixes; the reverse direction additionally uses existence of legal full extensions. Incomparable prefixes have disjoint cylinders without any positivity assumption. A prefix antichain has pairwise disjoint cylinders, but it covers the full space only with a separate branch-covering condition (such as a stopping set that meets every full branch).
12. The unrestricted full cylinder has `k^(K-m)` elements for a prefix of length `m`. A legal cylinder generally does not: its cardinality is the product of the numbers of positive piles in the remaining columns. Do not import the unrestricted homogeneous cardinality into the legal tree unchanged.

### Lexicographic order and time indices

13. Ordinary variable-length lexicographic order places a strict prefix before every strict extension. For equal-length words it is determined by the first unequal coordinate. A base-`k` numeral representation works for equal lengths but collapses leading zeros across different lengths (`0` and `00` both have numeral value zero), so it cannot by itself define the variable-length word order.
14. If two prefixes are incomparable and the first is lexicographically smaller, every full extension of the first precedes every full extension of the second. The incomparability condition cannot be omitted: `x = 0 <lex y = 00`, but the extension `01` of `x` lies after `00`.
15. Prefix cylinders are convex in the lexicographic order on full words. Their images among rows are contiguous only when the rows are sorted. Example: unsorted rows `00,10,01` give prefix `0` the disconnected position set `{0,2}` under zero-based indexing.
16. Prefix products use their actual column indices. A tail word appended after depth `m` must use profiles starting at time `m`, not the original profiles starting at time zero. The unshifted formula `weight(x ++ y) = weight(x) * weight(y)` is false in the inhomogeneous model. Example: first profile `(1,0)`, second `(1/2,1/2)`, `x = 0`, `y = 1`: the left side is `1/2`, while the unshifted right side is zero.
17. Column order must remain chronological as frozen in the matrix representation. Reversing columns can change the graph's location. For rows `01,01,10`, sorted equal rows occupy the first two positions. After column reversal the sorted rows are `01,10,10`, and the graph edge occupies the last two positions. These matrices have valid profiles `(2,1),(1,2)` and the reversed profiles respectively.

### Matrix and graph conventions

18. A shuffle matrix is an arbitrary labelled matrix with the prescribed column counts. A sorted row sequence is additional data obtained by a row permutation. Sorting preserves every column count and all prefix multiplicities. Do not encode every raw matrix as already sorted unless the separately required unsorted model remains available.
19. Every matrix entry witnesses a nonzero count of its value in that column; thus every row is legal. This is a deterministic counting lemma and needs no randomness.
20. The graph is an undirected subgraph of the path. For `SimpleGraph`, adjacency should include either adjacent orientation plus equality of the full row words. The one-sided predicate `j = i+1 ∧ row i = row j` is not symmetric and is not a `SimpleGraph` adjacency relation. An alternative frozen representation by edge starting indices is valid, provided the convention and translation to undirected edges are explicit.
21. Graph adjacency requires equality of full words, not merely a common proper prefix. A prefix block need not be one graph component: sorted `00,01` share prefix `0` but have no edge. A full-word block, if nonempty, is exactly one graph component. Equality of rows implies graph connectivity only after sortedness has been imposed; in unsorted `0,1,0`, equal endpoints are disconnected.
22. The count of graph edges contributed by a full word appearing `c` times is `c-1` with natural-number truncated subtraction, or `max(c-1,0)` over integers. At `c = 0`, the integer expression `c-1` is wrong. The assertion that the number of edges in a prefix block is strictly less than its row count requires that the block be nonempty.
23. Uniformity is on raw fixed-count matrices, not on distinct sorted row multisets. Example: `N = 3`, `K = 2`, both column counts `(2,1)`. Of the nine raw matrices, three sort to `00,00,11` and six to `00,01,10`, giving probabilities `1/3` and `2/3`, whereas uniformity over the two sorted outcomes would give `1/2` each.
24. Column independence is necessary for product-weight probability claims. It is not necessary for any deterministic legality, sorting, cylinder, interval, or graph lemma. With `N = 2`, both profiles `(1,1)`, and the two columns forced to be identical, the count of `00` is always one, whereas `N*weight(00) = 1/2`. This counterexample prevents importing a probabilistic expectation theorem from column counts alone.

### Endpoints, zero masses, and source corrections

25. Correct zero-based empirical endpoints are `L_w = #{i : take m (row i) <lex w}` and `U_w = #{i : take m (row i) ≤lex w}` for `m = length w`. Equivalently, with ordinary variable-length lexicographic comparison, use `L_w = #{i : row i <lex w}` and `U_w = #{i : row i <lex w OR w is a prefix of row i}`. The block is the positions `[L_w,U_w)` for zero-based indexing, and `(L_w,U_w]` for the source's one-based indexing. In either convention, its cardinality is `U_w - L_w`.
26. TeX lines 2951–2955 define `U_w = #{i : s_i ≤lex w}`. This is false under ordinary variable-length lex order for proper prefixes. Example: `N = 1`, sole full row `00`, and `w = 0`; the realized prefix block has cardinality one but both proposed endpoints are zero. The root gives an even stronger example: at positive depth every full row is strictly after the empty word, so that formula would give the entire deck upper endpoint zero. Freeze an explicit truncated comparison or the equivalent disjunction from the older papers, and document this source correction before implementation.
27. `2510.22783v1.pdf`, page 11, (2.15), says `t_x = E[ι(x)]/N`, while (2.13) gives `ι = L+1` and (2.16) says `λ_x` is the product mass. These are inconsistent: `Eτ/N - Eι/N = λ_x - 1/N`. Correct is `t_x = E[L]/N = (Eι-1)/N`. Prefer the exact finite cumulative-weight definition from the TeX and from `2103.05068v3.pdf` (2.1)–(2.3), which avoids this off-by-one typo entirely.
28. Deterministic intervals must be half-open: `J_w = [t_w,t_w+weight(w))`. At a fixed depth they are pairwise disjoint and cover `[0,1)`. Zero-weight words give empty intervals and can share endpoints; therefore strict endpoint monotonicity and distinctness of all endpoints are false. If “partition” means blocks are nonempty, index it by legal words rather than all words.
29. Prefix interval nesting and child partition identities are valid with actual time-dependent weights, including zero piles. The root interval is `[0,1)`. A terminal prefix interval can have positive length and still contains no nonterminal child intervals, so again terminal depth must be distinguished.
30. The point `1` is not in any `J_w`. The sentence on page 9 of `2103.05068v3.pdf` that samples `a ∈ [0,1]` and takes the unique containing interval is valid almost surely, not for every `a` in the closed interval. A deterministic unique-membership lemma must assume `a < 1`.
31. The source's `H_w = ℤ ∩ N J_w` is zero-based and can contain `0` while excluding `N`. Thus it is not automatically a subset of the one-based vertex set `[N]`. For the root, it is exactly `{0,...,N-1}`. Later clipping by `[N]` or a deliberate coordinate shift is necessary. Do not equate this deterministic lattice set with the one-based empirical block.

## Valid finite lemma candidates

The following are mathematically valid once the indicated data and conventions are frozen. They require no concentration, asymptotics, graph representation in law, or analytic hypotheses.

- Natural pile counts sum to `N`; normalized rational/real masses are nonnegative, at most one, sum to one, and are positive exactly at positive counts, under `N > 0`.
- Every actual column has a positive count; every legal prefix has a legal full extension; empty products equal one; prefix weight is nonnegative, at most one, and positive exactly for legal words within the depth bound.
- Prefix reflexivity, transitivity, antisymmetry, depth monotonicity, ancestor comparability, unique positive-depth parent, prefix-closed legality, root legality, and legal-child characterization.
- Full-prefix equality, root cylinder, terminal singleton cylinder, extension inclusion, common-extension comparability, disjoint cylinders for incomparable prefixes, and child partition strictly below terminal depth.
- A covering antichain partitions the full legal words; its realized cylinders give a disjoint union of realized row sets. Empty realized blocks are allowed.
- Linear/strict lexicographic order on equal-length words; compatibility with equal initial coordinates; lexicographic cylinder convexity; separation of incomparable ordered prefixes.
- Raw-matrix row legality; preservation of column counts and prefix counts under any row permutation; existence of a sorted row permutation; sorted prefix blocks are order-convex.
- Symmetry and looplessness of the path-equality graph; every edge joins equal words and adjacent indices; connectivity implies row equality; for sorted rows, equal words imply connectivity; a nonempty full-word block is a component.
- Corrected empirical endpoint membership and cardinality, including empty blocks; full-word edge count `count - 1` in naturals; prefix edge-count upper bound.
- At each depth, nonnegative word weights sum to one. Cumulative mass plus word mass is the non-strict cumulative mass. Deterministic intervals have the expected length, lie in `[0,1)`, are pairwise disjoint, and cover `[0,1)`; legal intervals are nonempty; illegal intervals are empty.
- Prefix deterministic interval containment and partition by one-letter legal children below terminal depth; tail factorization only with shifted profiles.
- If selected for the assigned scope: a lexicographic interval of full words is a union of an antichain of prefix cylinders. A quantitative `2Kk` bound needs the exact endpoint convention and treatment of the whole-space/root case fixed first; it is not implied by contiguity alone.

## Current review status

This is the independent pre-manifest review. The final theorem manifest has not yet been supplied. Every planned theorem must be checked against the frozen statements, especially the endpoint corrections and any claimed injectivity of the map from prefixes to cylinders.
