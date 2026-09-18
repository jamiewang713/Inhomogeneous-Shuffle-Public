# Independent adversarial review: stable-block decomposition

Role: hidden assumptions, counterexamples, and edge cases. This review was prepared independently of the argument and Lean-representation agents. Mathematical reading was restricted to the three sources specified by the user. No Lean code or mathematical source was edited.

## Verdict

The assigned boundary-family, retained-pair, stable-partition, and global-decomposition conclusions are valid with the source's intended finite legal-word model. There is a missing argument needed for the final global-coverage assertion: every compatible admissible pair is retained. It follows from genuine crossings and strictly positive legal-word mass, without adding a hypothesis. There is also a definition-domain problem for the parent in the unused first-crossing set when the ambient word already has terminal length. That domain issue must be resolved explicitly before freezing definitions.

The expected side-piece quantities must not be certified as actual fluctuation or anti-concentration scales: a downstream assertion fails because the article includes the first deterministic column in their maxima. This does not invalidate the assigned combinatorial partitions.

## Source assumptions and their exact roles

- Article lines 88–101: finite ordered alphabet with `k >= 2`, nonnegative integer pile sizes summing to `N` in each column, and a finite horizon. Although integrality/nonnegativity are implicit in the term “pile sizes,” they are needed for the probabilistic model. The finite combinatorial partition only needs each legal alphabet to be nonempty.
- `N > 1` is implicit in the asymptotic logarithmic-exponent setup (lines 95, 123, 474–488), but is not explicitly stated as a finite-`N` condition. Exact logarithmic definitions and monotonicity use it. Do not freeze a theorem asserting valid log-base-`N` exponents for `N = 1`.
- Article lines 446–458: legal words have positive pile size at each used coordinate; ambient words are legal; the prefix tree has depth at most `K`. Every legal prefix extends to a legal full word because every remaining column has some positive pile.
- Article lines 523–528: `0 < chi < 1/k` ensures a nonempty set of large digits. Its minimum and maximum have positive pile size. No assumption that every pile is positive, or that every column has two positive piles, is needed.
- Article lines 490–518: `c_L` uses the ambient exponent `b`, and subtracts nonnegative costs along descendants. Its exact equality to log expected size is not assumed; the article only gives equality up to `o(1)`. Avoid silently replacing `b` with an exact ambient log mass.
- Article lines 661–687: preserve the strict test `< delta` and complementary test `>= delta`, with source `delta > 0`. No strict decrease of `c_L` is required: probability-one columns give zero cost.
- The assigned combinatorial conclusions do not need the first-moment margin, profile regularity, good-column hypotheses, or exclusion of terminal fallbacks.

## Boundary prefixes and admissibility

Article lines 529–577 define a stopping family, not a collection of arbitrary crossing prefixes. For each full word, take the least index after the ambient length where its digit is strictly greater than the left boundary. If there is no such index, take the full terminal word. The right construction reverses the inequalities.

The family is an antichain. If one stopping word were a strict prefix of another, the shorter word cannot be terminal; at its last coordinate it has crossed, whereas the longer word's definition requires no crossing at that earlier coordinate. This is a contradiction. This also proves uniqueness without needing a secondary “shortest member” tie-breaker.

Equality to a large-pile boundary is not a crossing. A genuine crossing at time `K` is still a terminal prefix. If `K = |w|`, the terminal clause contributes exactly `w` on both sides, with an empty set of inspected coordinates. Columns with one positive pile cause no crossing on any legal path; the terminal clause makes the selection total.

The admissible subfamilies in lines 579–593 inherit the antichain property. Digits strictly below the minimum large digit, or strictly above the maximum large digit, have mass strictly below `chi`; equality at `chi` is included among large digits and causes no issue. Admissibility is simply a count bound and is not needed for any uniqueness argument.

## Compatible pairs, joins, fibers, and retention

For words on one path, two prefixes are comparable. Hence article `A_{y,z}` is nonempty exactly when `y` and `z` are comparable, and then its members are precisely legal descendants of the longer word `v = y join z`. Equal lengths under compatibility force equal words, so the join has no ambiguous tie case.

For a compatible boundary pair, the full-string fiber

`{omega in B_w : L(omega) = y and R(omega) = z}`

equals `B_v`. One inclusion follows from taking prefixes; the other uses the antichain uniqueness of each boundary selection. This equality is an essential helper for interpreting the global statement at article lines 828–855. Furthermore, comparable joins of two compatible boundary pairs imply equality of both pairs: their left prefixes lie on the same path and belong to one antichain, and likewise for their right prefixes. Thus distinct compatible joins are themselves an antichain.

The missing retention proof is as follows. If a compatible pair is terminal, it is retained by definition. Otherwise `|y| < K` and `|z| < K`, so both must come from the genuine-crossing clauses. At time `i = |y|`, replace `v[i] = y[i]` by the minimum large digit. Keep every other digit of `v`. This produces a legal word of the same length belonging to `P_{v,i}`. Its expected count is positive because `N * product_j (n_digit^(j)/N) > 0`. The corresponding maximum is therefore positive. Replacing at the right crossing by the maximum large digit gives a positive right maximum. Both maxima are finite, so both square-root logarithms are finite for `N > 1`. Therefore every compatible admissible pair is retained. This is derived from the source assumptions, not an extra regularity hypothesis.

Consequently, the final assertion at lines 842–844 is correct: an uncovered full string has at least one inadmissible selected boundary prefix. Its selected pair cannot be a further discarded compatible pair of zero fluctuation.

## Fluctuation pieces

Article lines 607–618 define sets of prefixes at the length of `x`. Different coordinates give disjoint first-difference pieces, and their unions represent exactly the words lexicographically to the left or to the right of `x` inside the ambient block.

The statement at lines 640–643 is correct at the level of represented full strings and random counts: for `i <= |v|`, the union of cylinders represented by `P_{x,i}` depends only on coordinates of `x` through `i`, hence only on `v`. The same is true on the right. The suffix after coordinate `i` is unrestricted, so completing all legal prefixes to full words removes the apparent dependence on `|x|`.

Do not freeze literal equality of prefix families at different lengths. For instance, with three legal digits at each time, `P_{[1],1}` contains the one-digit word `[0]`, whereas `P_{[1,0],1}` contains `[0,0]`, `[0,1]`, and `[0,2]`. Their represented full-string sets, rather than the prefix families themselves, are equal.

Empty maxima have value zero as stated at line 639. Their logarithms have value negative infinity, not the real value zero. Terminal retained pairs may have such a value. Separate the terminal branch before taking real subtraction by the fluctuation exponent; do not coerce negative infinity to a finite real.

## Parent-domain defect and a faithful implementation boundary

The source defines the parent only for nonroot words (line 458), and `c_L` only for extensions of `w` (line 497). Yet it writes `Gamma` for all pairs using `c_L(parent x)` (lines 661–675).

If `K = |w|`, then the sole compatible pair has `v = w`. For its sole candidate `x = w`, `parent x` either is undefined (when `w` is empty) or is not an extension of `w`. The displayed expression is outside the stated domain. The stable-family terminal branch never uses it, so the partition itself remains meaningful.

Before freezing, give the first-crossing predicate its intended domain where the parent is an ambient extension, and construct the terminal stable family separately. An alternative is an explicitly documented total parent/exponent convention, but its values outside the source domain must not be imported into a theorem as if the article specified them. Do not add `|w| < K` as a new assumption to the global decomposition, because that would exclude a required terminal case.

For a nonterminal pair, `|w| < |v|` is derived from the boundary definitions, and every candidate parent is an ambient extension. In the stopping branch where `score(v) >= delta`, `v` itself cannot satisfy `Gamma` because `Gamma` requires `score(v) < delta`; actual first crossings are strict descendants of `v`.

## Stable stopping, singleton cases, and antichains

For a nonterminal pair, fix the finite constant fluctuation exponent and define `score(x) = c_L(x) - c_F(v)`. This score is nonincreasing along prefixes. If its value at `v` is below the threshold, the stable family is exactly `{v}`. Otherwise each full path has either a least descendant of score below the threshold or no such descendant. In the former case the immediately preceding score is at least the threshold, giving a `Gamma` member; in the latter case the terminal word belongs to `Lambda`.

First crossing at length `K` belongs to `Gamma`. Score equality at `K` belongs to `Lambda`. The two sets are disjoint because their score inequalities are complementary. A descendant of a `Gamma` member has score below the threshold, so cannot be a fallback; if it is a strict descendant, its parent already has score below the threshold, so it cannot be another first crossing. Different terminal words are incomparable. These observations establish the antichain needed at lines 817–825.

Distinguish the source's branch singleton `{v}` from cardinality-one stable families. Cardinality one alone does not imply `{v}` when fallback is permitted. Concrete example: `k = 3`, `N` a sufficiently large multiple of three, `w` empty, `K = 2`, first column equal thirds, and second column entirely digit zero. Take `chi < 1/3`, `y = z = [1]`, `b = 1`, and `0 < delta < (1 - log_N 3)/2`. Then `c_F(v) = (1 - log_N 3)/2`, the remaining digit has zero cost, `Gamma` is empty, and `Lambda = {[1,0]}`. Thus the stable family has cardinality one but is not `{v}`. The partition remains correct. Statements about “singleton stability inequality” must use the definition branch or the exact equality `Stable = {v}`, not just cardinality one.

## Lexicographic intervals and random realizations

Each individual prefix cylinder is convex in lexicographic order. Under a nondecreasing list of sampled full words, its inverse image is therefore an order-convex set of positions, possibly empty. Prefix antichains give pairwise disjoint cylinders; their inverse images are pairwise disjoint and union to the parent interval. Repeated sampled words pose no problem because each position has one full word and that word has one selected stable prefix.

Random intervals need not be nonempty even for legal prefixes. For example, with `N = 2` and two columns each containing one zero and one one, the legal prefix `[0,0]` is absent whenever the columns place their zeros in different rows. Thus the formal meaning of “partition” should be pairwise disjoint union equality, allowing empty occupied intervals, unless empty intervals are explicitly removed. Do not use a nonempty-block partition API without addressing this.

An arbitrary antichain union need not be a single interval: with three legal first digits, `{[0],[2]}` omits the middle cylinder. The notation `I(U)` at lines 455–457 should not confer contiguity on every antichain family. Individual cylinders and the particular first-difference pieces are convex; arbitrary unions need not be.

## Relation to the two previous papers

- `2510.22783v1.pdf`, pages 18–19, Definition 4.3 and equation (4.5), supplies the earlier boundary-family and side-piece construction. Its page 25, Lemma 4.9, proves a partition after asserting leaf crossing using a tail margin. The current article's terminal and fallback branches remove the need to assume this analytical leaf-crossing fact for the combinatorial partition.
- That earlier PDF has apparent transcription/typesetting problems in the displayed right-family definition (page 18). The current article's explicit time-`K` clauses are the operative definitions; do not silently copy the older formula over them.
- `2103.05068v3.pdf`, pages 20–21, Lemmas 4.5–4.6, obtains a partition from leaves of a full `k`-ary stopping subtree. The current legal tree need not be full `k`-ary because zero piles are allowed. Its proof principle survives as “every legal full path reaches exactly one stopping prefix”; importing a full-`k`-ary hypothesis would be unjustified.

## Concrete downstream failure relevant to freezing meanings

Article lines 623 and 628 include the first ambient coordinate in both side maxima. For the whole deck, take `k = 3`, equal deterministic pile sizes in the first column, `w` empty, `K >= 2`, and `chi < 1/3`. Let `y = z = x = [1]`. Both boundaries genuinely cross at time one. The pair is admissible, nonterminal, retained, and fluctuation-regular: `c_F(x) = c_L(x)/2 = (1 - log_N 3)/2`, and later `c_L` cannot increase.

Nevertheless the sorted interval for `[1]` consists deterministically of the middle `N/3` positions. Both endpoints are deterministic. The anti-concentration conclusion at lines 1228–1237, asserted for every `x in A_{y,z}`, would bound an endpoint atom close to one by `N^(-1/2 + O(delta) + o(1))`, and fails as the small threshold is chosen sufficiently small. Increasing `K` so numerical first-moment margins hold does not remove this first-column obstruction.

The older `2510.22783v1.pdf` deliberately excludes coordinate one from the fluctuation maxima (page 19) and explicitly explains on page 23 that deterministic first-column counts make initial-digit blocks predictable. This is a real difference, not a proof detail that can be supplied by an extra trusted lemma. The assigned decomposition can be formalized, but an anti-concentration bridge for these frozen quantities must not be claimed without a corrected source statement.

There is also a lesser exactness issue outside the assignment: line 1700 writes `s = T` for terminal pairs, whereas the definitions give `s = K/log N = floor(T log N)/log N`; equality holds only up to an `O(1/log N)` discrepancy. This does not affect the finite combinatorial proof.

## Review of the proposed finite representation

After completing the independent audit, I reviewed the parent agent's proposed representation. The following choices are faithful with the stated safeguards:

- Words may be total lists of natural numbers, with legality requiring length at most `K`, digits less than `k`, and positive count in each used column. A total digit accessor and total `parent(x) = take(length(x)-1,x)` are harmless outside the source domain. A total exponent given by the same finite-sum formula is likewise harmless, provided source theorems are about legal ambient extensions and the active first-crossing proof derives that its parent is an ambient extension. This totalization must be documented before freezing.
- A total count function `n : Nat -> Nat -> Nat` should have its normalization assumption only at the finite source times `j < K`; values at unused later times need no constraint. Only legal digit positions enter source claims.
- `expectedCount(E) = N * sum_{omega in (Fin K -> Fin k)} 1_E(omega) * product_j(n(j,omega(j))/N)` is the exact one-row marginal expected count for independent column permutations. It does not assert independence between different rows. This finite formula suffices for nonnegativity, normalization, and positivity of legal cylinders.
- The full-string sample space `Fin K -> Fin k` still contains illegal strings when a pile is zero. Source cylinders must either include a legality condition or be defined in the legal full-string subtype; zero probability alone does not make illegal words absent from a deterministic set identity.
- A `WithBot Real` exponent represents the stated `log(0) = -infinity`. Comparing `c_L(x) < c_F(v) + delta` agrees with the source subtraction comparison whenever `c_F` is finite. In the terminal branch no such comparison is required. For compatible nonterminal boundary pairs, finiteness is derived from genuine crossings.
- A generic persistent-stopping theorem may quantify over an arbitrary predicate with a proved persistence premise. Applying it after proving persistence of the source threshold predicate introduces no new model assumption. The concrete theorem must not take threshold persistence, antichains, retained coverage, or parent legality as unproved project hypotheses.
- An arbitrary ambient proxy `b` is correct for the finite partition theorems. An exact equality between `c_L` and log expected count would be a different statement and cannot be asserted from this representation alone.
