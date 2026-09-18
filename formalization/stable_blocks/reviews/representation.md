# Independent representation review

Role: design the Lean representation and theorem interfaces before implementation.

Mathematical sources read: `time_inhomogeneous_riffle_shuffle_unified_article.tex`, especially the common setup and lines 440–1050; `2510.22783v1.pdf`, Definitions 4.3 and the argument around Lemma 4.9; `2103.05068v3.pdf`, the stable-tree construction and Lemmas 4.5–4.6. No other mathematical sources were used. PDF text extraction is derived from the supplied files.

## Recommended exact finite representation

The core combinatorial model has alphabet `Fin k`, full words `Fin K → Fin k`, and prefixes `List (Fin k)`. A prefix is legal when its length is at most `K` and every selected pile count is positive. A legal ambient prefix `w` is fixed. Prefixes use the existing list prefix relation. Zero-based Lean position `i` corresponds to paper position `j=i+1` throughout.

Pile data are `n : Nat → Fin k → Nat`, with `∑ a, n i a = N` at every `i<K`. The intended logarithmic model has `2≤k`, `1<N`, and `0<χ<1/k`. Here `1<N` makes explicit the domain of the paper's base-`N` logarithms; this must be recorded at freeze rather than introduced in a proof. The stopping parameter is the source's `δ>0`; `b` is arbitrary real ambient exponent. The boundary-count cutoff is exactly `C/log(1/χ)*log N`, with the source's non-strict `≤` admissibility inequality.

`B x` is the set of full legal words whose first `x.length` digits equal `x`. A prefix-family cylinder is the union of its individual cylinders. An arbitrary row map `rows : Fin N → FullLegalWord` gives `I B = {i | rows i ∈ B}`. Probability is unnecessary for the partition transfer. For contiguity require that `rows` is nondecreasing in lexicographic order; this is precisely the source's sorting operation.

The exact expected occupancy can be represented without an entire random-matrix API by

`ExpectedCount E = N * Σ ω : (Fin K → Fin k), (if E ω then ∏ i, n i (ω i) / N else 0)`.

This is the actual one-row marginal formula in the source model, because columns are independent uniform permutations of their fixed multisets. A later shuffle-matrix foundation must prove the expected-card-count identity to connect this deterministic finite expression to expectation notation. The decomposition theorem itself must not take positivity or continuation invariance of an arbitrary expectation oracle as an extra assumption; both follow from this finite definition.

`parent x := x.dropLast` is total, including `parent [] = []`. This convention affects no source use: in every nonterminal stable branch the join is a proper extension of `w`, hence every `Gamma` element whose parent is used is nonempty. Prove this fact explicitly. Terminal root/leaf case `w.length=K=0` is treated by the terminal singleton branch.

For compatible prefixes, `join y z` selects the longer one, taking `z` in a tie. Equality of equally long comparable prefixes makes this choice immaterial. Do not define join as coordinatewise maximum or longest common prefix.

Fluctuation exponents live in `WithBot ℝ`: zero fluctuation maps to `⊥`, and strictly positive fluctuation maps to its ordinary real logarithm. No `+∞` can occur. Define the stopping test by

`(cL x : WithBot ℝ) < cF (join y z) + (δ : WithBot ℝ)`.

For finite `cF` this is exactly the paper's `cL x - cF < δ`; for `cF=⊥` it is false, agreeing with the source's `cL-(-∞)=+∞` interpretation. State this equivalence explicitly. The terminal branch precedes this test, so terminal pairs with vanishing fluctuations remain singleton stable families.

## Definitions that must be frozen

1. `Legal`, `Extends`, `FullLegalWord`, prefix cylinder, family cylinder, and ambient cylinder.
2. Left and right large-pile boundary indices: the minimum and maximum digits whose masses are at least `χ`. Their existence is derived from the column sum and `χ<1/k`.
3. Left boundary family: a first strict crossing `x[last]>left[last]` after `w`, with all earlier post-ambient digits `≤left`, or a full terminal word with all post-ambient digits `≤left`. The right family reverses both inequalities. Crossing at time `K` is allowed in both definitions.
4. `L(ω)` and `R(ω)` as the unique boundary prefixes along the full word; use a least crossing index or the terminal length if no crossing exists.
5. Small-pile violation counts: positions from `w.length` through `x.length-1` with digit strictly below the left boundary, or strictly above the right boundary. Admissibility is count cast to real `≤ C/log(1/χ)*log N`.
6. A boundary pair includes genuine membership in the two boundary families. A compatible pair has a common legal descendant; equivalently one component extends the other. Its `A` family is exactly the legal descendants of its join.
7. `P(x,i)` and `Q(x,i)` are legal prefixes of length `x.length`, extending `w`, equal to `x` before position `i` after `w`, and having respectively a smaller/larger digit at `i`; later digits are unrestricted. They must not be defined by fixing all later digits.
8. Left/right fluctuation is the square root of the maximum expected occupancy of these side families over `w.length ≤ i < join.length`. Empty maxima are zero. Both sides use the join length in the current article, although the old paper uses different limits.
9. `cF` is the minimum of the two extended logarithms. Continuation invariance is a theorem, not a model field.
10. Terminal means `y.length=K ∨ z.length=K`. Retained means compatible and either terminal or finite/nonbottom `cF`. Admissibility remains a separate condition.
11. `Gamma`: legal descendants of the join with the stopping test true and the same test false at their parent. `Lambda`: full legal descendants of the join with the stopping test false. Keep the source's strict test and complementary non-strict test.
12. Stable family: terminal singleton; otherwise singleton if the join passes the strict test; otherwise `Gamma ∪ Lambda`.

## Required theorem schemas and dependencies

The following catalog states semantic schemas; concrete Lean names can be fixed with the final interface. Algebraic list/finite-sum helper lemmas should be covered by the same freeze, not used to change the source statement.

### Word and order foundations

- Prefix reflexivity/transitivity/antisymmetry; prefix length monotonicity; equal-length prefix equality.
- Two prefixes of one word are comparable; the shorter prefix is the corresponding `take` of the longer.
- Prefix restriction preserves legality; a legal prefix has a legal full extension, using a positive pile in every remaining column.
- `B x` is nonempty for legal `x`; `B y ⊆ B x` when `x` prefixes `y`.
- `B x ∩ B y` is empty for incomparable prefixes and equals the longer-prefix cylinder for comparable prefixes.
- A prefix antichain has pairwise disjoint cylinders.
- A prefix cylinder is convex in lexicographic order among full legal words.
- Inverse images under a sorted row map of prefix cylinders are order-convex subsets of `Fin N`; inverse images preserve disjointness and unions.

### Boundary cuts

- A large-pile digit exists; the selected left/right digits have positive legal counts and left `≤` right.
- Every left/right boundary-family prefix extends `w` and is legal; every nonterminal member has a genuine last-position crossing and length strictly greater than `w.length`.
- Each boundary family is a prefix antichain, including terminal members.
- Every full legal word in `B w` has exactly one left and exactly one right boundary-family prefix. Its selected prefix is the least strict-crossing prefix; if no crossing occurs it is the full word.
- For a boundary-family element `y`, `L ω = y` iff `ω ∈ B y`; similarly on the right.
- A common descendant exists iff the boundary prefixes are comparable. The join is legal, extends `w`, and has length equal to the maximum component length.
- The boundary-pair fiber is exactly `B(join y z)` when compatible, and empty otherwise.
- Distinct compatible boundary pairs have disjoint join cylinders. Consequently the raw boundary-pair fibers form a disjoint cover of `B w`.

### Side pieces and retention

- A full word belongs to the cylinder union of `P(x,i)` iff its digits before `i` equal those of `x` and its digit at `i` is smaller; similarly for `Q`.
- These first-difference pieces are pairwise disjoint for different positions; their union is the legal full-word part to the left/right of `x` at depth `x.length`, inside the ambient cylinder.
- If `v` prefixes `x` and `i<v.length`, then the cylinder unions of `P(x,i)` and `P(v,i)` are equal, and similarly for `Q`. Therefore expected masses, fluctuations, and `cF` are identical beyond a boundary join.
- Every full legal word has strictly positive product weight; any event containing one such word has strictly positive expected occupancy.
- A genuine left crossing supplies a legal full word in the corresponding left side piece by changing its crossing digit to the left large-pile digit; a genuine right crossing supplies the analogous right word.
- Every compatible nonterminal boundary pair has positive fluctuation on both sides. This uses the two genuine crossings, not local-good assumptions or fluctuation regularity.
- Hence every compatible boundary pair is retained; in particular admissibility cannot remove a compatible pair by a second zero-fluctuation exclusion.

The last result is indispensable for the final sentence of the source's global-decomposition lemma. Merely proving a partition conditional on retention would not establish that only inadmissible strings are lost.

### Stable stopping cut

- The concrete score `cL` is nonincreasing along legal extension. Each increment subtracts a nonnegative quantity because `0<n_i(digit)≤N` and `log N>0`.
- The strict stopping predicate is persistent under legal extension because `cF(join)` is fixed.
- Generic finite-tree stopping theorem: for a fixed legal root and an extension-persistent predicate, choosing the root if it is already stopped, otherwise the first stopped descendant or an unstopped terminal word, gives exactly one selected prefix on every full root-to-leaf path.
- Least-crossing existence/minimality: if any descendant on a finite path passes the strict test, its least passing length has a parent that fails it. In the root-above-threshold branch that least length is strictly larger than the root length. If there is no crossing, the terminal word lies in `Lambda`.
- A `Gamma` prefix has no strictly longer selected descendant. A `Lambda` prefix is a leaf. `Gamma` and `Lambda` are disjoint.
- The stable family is a prefix antichain in all three definition branches.
- Every full legal word under the join has exactly one stable prefix.
- The stable cylinders are a pairwise disjoint cover of the join cylinder.
- Their sampled index sets are pairwise disjoint, order-convex, and cover the join's sampled index set.
- Terminal stable families are singleton joins, including `w.length=K`. Root-already-crossed stable families are also singleton joins. The descendant branch may itself happen to contain one prefix: branch identity is not equivalent to cardinality greater than one.

### Global retained decomposition

- A full ambient word is covered by a retained admissible stable cylinder iff both of its unique boundary prefixes are admissible.
- Indexed by the boundary pair and its stable prefix, all retained admissible stable cylinders are pairwise disjoint.
- Their union is exactly `{ω∈B w | admissibleLeft(L ω) ∧ admissibleRight(R ω)}`.
- Its complement within `B w` is exactly the words whose left or right selected prefix fails admissibility.
- Apply inverse-image identities under the sorted row map to obtain the same statements for sampled intervals.

## Foundational Lean modules needed previously

1. Finite words: bounded legal prefixes, finite full words, restriction/extension, prefix order and lexicographic order.
2. Cylinders and sampled intervals: cylinder intersection, antichains, lexicographic convexity, inverse-image disjoint-cover transfer. This module can be deterministic and independent of probability.
3. Fixed-column product masses: finite sums/products, normalization, positive support, marginal sums and exact expected-count formula. The one-row marginal identity is the bridge to a future random-matrix module.
4. Extended fluctuation exponents: real square root/logarithm, zero-to-bottom convention, finite maxima, `WithBot` comparisons and the real-subtraction equivalence.
5. Finite monotone stopping cuts: first-index existence, minimality, prefix antichain and cover, with terminal fallback.
6. The larger paper separately needs shuffle permutations/graphs, conditional uniform column allocation, hypergeometric concentration and anti-concentration, entropy and profile estimates, exponential moments, total variation and random-cut mixtures. None should be smuggled into a structural partition theorem as an unproved axiom.

Possible mathlib dependencies are list prefix/lex APIs, `Fin` and finite function enumeration, finite sums/products, ordered sets and `OrdConnected`, real logarithm and square root, and `WithBot`. Exact import names must be checked against the installed version; this report does not claim that uninspected declarations exist under particular names.

## Edge cases and source distinctions

- At ambient terminal depth, both boundary selections equal `w`, their join is `w`, and the stable family is `{w}` even if both fluctuation maxima are zero.
- A crossing at time `K` is terminal, not a nonterminal regular fluctuation case.
- Simultaneous crossings can give `y=z`; equal lengths must be handled without requiring strict comparability.
- Zero-sized piles are allowed and excluded only by legality. Strictly positive masses for every alphabet digit would be an unauthorized strengthening.
- Legal full cylinders are nonempty, but their sampled row intervals may be empty. A sampled 'partition' is a pairwise disjoint cover allowing empty sets, not a partition object requiring all parts to be nonempty.
- A terminal join represents one full legal string; the sampled interval of that string can contain many cards.
- No tail-size margin, local-good hypothesis, homogeneity hypothesis, or endpoint anti-concentration estimate is needed to prove the stable partition after `Lambda` is included.
- Do not omit `Lambda` based on the old homogeneous paper's tail estimate. The current article deliberately makes the stopping rule total before applying that estimate.
- The old 2025 PDF has a special first-column convention and apparent typographical asymmetries in Definition 4.3. The current article's explicit ambient-relative left/right definitions control this formalization.

Verdict: the assigned structural statements are consistent with the proposed exact finite representation. The main obligations that a superficial translation would miss are the positivity-to-retention implication, cylinder-level continuation invariance, and first-crossing minimality before asserting antichain disjointness.
