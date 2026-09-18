# Independent reconstruction of occupancy-conditioned internal edges

I reread the relevant TeX passages and the optional O.D01–O.D02/O.01–O.07 inventory in `collision_contract_statements.md`, section 7, against the now-proved collision model. All seven proposed lemmas are mathematically valid with their stated domains. They require three new definitions grouped under O.D01–O.D02 and exactly seven new named lemmas. The intermediate calculations below can remain local proofs; no additional named Fubini, conditional-law, row-concatenation, or enumeration theorem is needed. This report does not modify either previous freeze and contains no Lean implementation.

## Source meaning and fixed parameters

The source law is uniform among matrices with the prescribed deterministic counts in each column (TeX 388–392). The particular source assertion addressed here is TeX 1516–1523: the internal-edge count conditioned on the number of rows with a fixed absolute prefix is bounded by that number squared times the product of suffix two-label coincidence factors. The exact pair-count argument actually gives the smaller coefficient `choose q 2`. This is a strengthening proved from the original law, not an assumption about conditional independence.

Let N, K, k, M be natural numbers; let n assign k pile counts to each of K columns, with each column sum equal to N; let M ≤ K; and let x be a fixed word in `Fin M → Fin k`. The original N is retained in every suffix column, every fixed-column sample type, and the denominator N(N−1). Selecting q labels by their prefix does not remove the other N−q labels from the suffix experiment or replace deterministic suffix counts by counts summing to q.

This conditioning is narrower than the internal information at TeX 1210–1212, which includes continuation strings, and narrower than the exploration sigma-field at 1923–1943. No endpoint smoothing, ambient variance transfer, or preservation of a residual exploration law is proved here. The wording about an ambient initial population at 1249–1258 does not justify changing the fixed-column denominators in the source's explicit formula at 1522. The different operation at 3138–3166 fixes prescribed row symbols in each column, removes those rows, and obtains genuinely reduced counts and population. That separate residual model is not used in O.01–O.07.

## Exact definition inventory

O.D01 contains `prefixCounts` and `suffixCounts`. Both take the count array n and the proof M ≤ K. At a prefix index t the column is n at t; at a suffix index u the column is n at M+u. They do not take N, because restriction does not depend on population. Their coordinate sum proofs are the corresponding applications of the given column-sum proof, supplied inline to the existing `matrixLaw` constructor.

O.D02 contains `splitMatrix`. It takes explicit N, n, and M ≤ K, and maps a full matrix to its restrictions to the two coordinate intervals. Explicit N is necessary because n and the inequality do not determine it. Its inverse uses the prefix array at j when j<M and the suffix array at j−M otherwise. The identities j=(M+(j−M)) in the second case and equality of count indices justify the dependent transports. Both inverse laws follow coordinatewise, splitting explicitly at j<M. The existing derived function/product Fintype instances suffice; no new named instance is required.

For the remainder, P and T denote the prefix and suffix matrix spaces, W, Wpre, and Wtail denote their existing matrix laws, and g(p,t) denotes `(splitMatrix N n hM).symm (p,t)`. These are report notation, not extra project definitions. Write Z for the sorted full-deck occupancy of x, z(p) for its raw prefix-array occupancy, and Q for `tailCollisionFactor N n M`.

The theorem parameter policy should preserve the completed core's explicit arguments: every scalar tail factor takes N first; every occurrence of raw or sorted rows takes its own count array; `splitMatrix` takes explicit N. O.02 is a pure product identity and takes no column-sum proof. O.03 takes actual prefix and suffix samples and no unused sum proof. O.04 takes only its arbitrary finite subset of natural labels. O.01 and O.05–O.07 take the original n, column-sum proof, and M ≤ K; O.05–O.07 also take x, followed by p or q as appropriate. No final theorem gains N≥2, q≤N, positive pile counts, or a positive event-probability premise.

## O.01: `matrix_expectation_split`

The exact assertion is

`E_W f = E_Wpre [p ↦ E_Wtail [t ↦ f(g(p,t))]]`

for every real-valued function f on the full matrix space, without sign restrictions.

Use C.17 to replace each of the three matrix weights by the inverse of its sample-space cardinality. Let these cardinalities be C, A, and B. `Fintype.card_congr` for `splitMatrix`, followed by `Fintype.card_prod`, gives C=A*B. Consequently the full weight of g(p,t) equals the product of the prefix and suffix weights. The real inverse-of-product identity is valid even at zero; feasibility already derives inhabitance of the spaces, so no extra cardinality-positivity hypothesis is needed.

Expand the frozen finite expectation, reindex its sum through the equivalence, and express a sum over P×T as nested finite sums. Substitute the weight identity and distribute the prefix weight through the inner sum. This proves O.01 using only C.17, existing definitions, and trusted finite-sum identities. The weight identity, cardinality calculation, and finite-sum reindexing can all be local `have` proofs. There is no reason to add a named general Fubini helper or a probability pushforward structure.

## O.02: `tailCollisionFactor_suffix`

The assertion is

`tailCollisionFactor N (suffixCounts n hM) 0 = tailCollisionFactor N n M`.

Every suffix-coordinate index satisfies 0≤u, so the left product ranges over all `Fin (K−M)`. Map u to M+u. Its image is exactly the original column-index finset satisfying M≤j. The inverse is j−M, whose bound j−M<K−M follows from j<K and M≤j. The summand coincidence factors agree by the definition of `suffixCounts`. A local finite-product bijection proves the identity. At M=K both index sets are empty and both products equal one. The argument does not use column feasibility or N≥2.

## O.03: `prefix_occupancy_glue`

The assertion is the equality of the raw full-deck occupancy in g(p,t) with the raw occupancy in p. Apply C.21 to each actual row label, once for the full array and once to the M-column prefix array with the length bound M≤M. Both prefix events state that the same first M entries equal x. Restriction followed by gluing has those entries exactly equal to p's entries; this follows by the prefix branch of the equivalence inverse, including its count-index transports.

For an implementation that avoids unfolding dependent inverse transports, apply `congrArg` to the prefix-coordinate projection of `splitMatrix.apply_symm_apply (p,t)`. This directly gives the needed glued prefix-digit identity because the forward map is literal restriction. The suffix-coordinate projection gives the corresponding suffix identity for O.05. These are proof-only local steps, not assumed coordinate bridges.

Use C.20a for natural labels in `range N`, and extensionality of the occupied finsets to get cardinal equality. Values outside the deck are irrelevant. C.30 then gives locally

`Z(g(p,t)) = z(p)`.

This proves deterministic suffix-independence of the occupancy observable, not an assumption about a conditional law. The needed coordinate identities can remain local here and in O.05.

## O.04: `increasing_pairs_in_finset_card`

For arbitrary `s : Finset ℕ`, the increasing pairs in s×s have cardinality `Nat.choose s.card 2`. This does not require s to be an interval or nonempty.

A bounded proof route uses the trusted `Finset.orderIsoOfFin s rfl`. Its increasing enumeration identifies the increasing pairs in `range s.card` with those in s. The inverse is the order isomorphism's inverse applied to each member of s. C.37 supplies the cardinality on the range side. All natural-index conversions and the pair bijection are local. Empty and singleton sets need no special nonempty argument: the order isomorphism and C.37 already include them.

An alternative, if the order-isomorphism interface is cumbersome, is a local partition of the off-diagonal pairs into the two strict orientations. Swapping coordinates bijects those parts, and the off-diagonal count is s.card*(s.card−1); the binomial identity finishes. Neither route changes the theorem or needs another named lemma.

## O.05: `tail_expected_collisionPairs_given_prefix_array`

For each fixed prefix array p, the exact assertion is

`E_Wtail [t ↦ #collisionPairs(sortedRows(g(p,t)),x)] = choose(z(p),2) * Q`.

Let s be the finite set of original labels whose row in p carries x. It is deterministic under the tail expectation, is contained in `range N`, and has cardinality z(p). O.03's cardinal equality alone is insufficient for the next step: prove locally, for every actual label i, that its glued row carries x if and only if its prefix-array row carries x. This follows from C.21 and the coordinate projections of the split equivalence's inverse law. For two labels in s, prove locally using C.22 that their full glued rows are equal if and only if their suffix-array rows are equal. The forward implication restricts equality to suffix columns; the reverse implication uses their common prefix x for j<M and suffix equality for j≥M.

These pointwise equivalences show that an increasing pair of labels from s is a collision pair of the full glued matrix precisely when its two suffix rows agree. Conversely, full-row equality and x-prefix membership put both labels in s; membership of the second label follows by equality of the prefix rows. No full row-concatenation theorem or other coordinate helper needs to be named.

First apply C.31 samplewise to replace sorted collision cardinality by raw cardinality. If N=0 or N=1, C.48–C.49 make every full collision count zero. Also z(p)≤N, by the occupied-set inclusion in `range N`, so `choose(z(p),2)=0`. This proves those branches without using a distinct-label formula.

In the N≥2 branch, use F12 on the deterministic increasing-pair set of s. For each pair, its natural labels give distinct members of `Fin N`. C.33 for the suffix matrix, with the unique empty prefix represented by `Fin.elim0`, gives the tail-row equality probability. C.57 sets the empty prefix-pair factor to one, and O.02 identifies the remaining suffix collision product with Q. Hence every pair contributes Q. O.04 counts the pairs, giving the formula. An empty or singleton s makes the sum empty even in this N≥2 branch.

The probability supplied by C.33 is the original two-label fixed-column probability, with denominator N(N−1). It is not a product law on only the selected labels. This is the central conditioning check.

## O.06: `matrix_collisionPairs_occupancy_slice`

For every natural q, without a probability-positivity or range premise,

`E_W [1_(Z=q) * #collisionPairs(sortedRows,x)] = choose(q,2) * Q * P_W(Z=q)`.

The Lean statement can retain the proposed `if Z=q then count else 0` representation. Apply O.01 to that integrand. By O.03 and C.30, the indicator becomes `z(p)=q` and is constant while integrating the suffix. Split on this equality for each p. On the true branch O.05 gives `choose(z(p),2)*Q = choose(q,2)*Q`; on the false branch the inner expectation is zero. Expanding the outer finite expectation factors out this constant and leaves the prefix-law probability of `z(p)=q`.

Apply O.01 again to the indicator of the full event. The same deterministic occupancy identity and F03 for a constant inner expectation show that this prefix-law probability is exactly `P_W(Z=q)`. These indicator and scalar expectation calculations can remain local. The proof never divides by the event probability and does not normalize a law on the slice.

## O.07: `matrix_internal_edges_occupancy_slice`

For every natural q,

`E_W [1_(Z=q) * edgeCount(sortedRows,x)] ≤ choose(q,2) * Q * P_W(Z=q)`.

Split pointwise on Z=q. On the true branch the frozen F21 injects each internal edge into a collision pair, and the natural cardinal inequality casts to reals. On the false branch both integrands are zero. Apply frozen expectation monotonicity F02 and then O.06. There is no squaring step, localization assumption, or event-dependent graph reindexing in this proof.

For a positive-probability slice, dividing this already-proved finite identity or inequality would yield the usual conditional expectation interpretation. Such a normalized theorem is not part of the proposed inventory. The source's weaker q² coefficient at 1520 follows mathematically from `choose q 2≤q²` and Q≥0, without altering any definitions.

## All degenerate cases

* **N=0:** occupied, collision, and edge sets are empty. The only possible occupancy is zero. All slice count expectations vanish, including when the suffix product is an empty product equal to one. O.05 explicitly resolves this branch before pair probabilities.
* **N=1:** occupancy is at most one, so every collision coefficient and every internal-edge count is zero. A nonempty suffix has zero numerical pair factors because the total real division uses a zero denominator, but no pair probability is invoked in this branch; an empty suffix has product one and remains harmless.
* **q=0 or q=1:** the coefficient `choose q 2` is zero. O.06 gives zero collision expectation on the slice. O.07 and nonnegative expectation imply zero internal-edge expectation on the slice.
* **q>N:** every occupancy is at most N, so the event is false. Its probability and both indicated expectations are zero, even though `choose q 2` may be positive. No q≤N assumption is permitted or needed.
* **A null slice of any other kind:** the right side of O.06 is zero and the left side follows from the exact division-free proof. The nonnegative left side of O.07 is also zero. Neither statement defines conditional probability on a null event.
* **M=0:** the prefix array is the unique empty family, all N labels are occupied, and only the q=N slice can occur. O.05 reduces to the already-proved empty-prefix tail collision formula.
* **M=K:** the tail array is the unique empty family and Q=1. All occupied rows carry the same full word, so their collision count is exactly `choose z(p) 2`.
* **K=0:** M=0 and all row words are empty. The matrix space is a singleton, collision count is `choose N 2`, and edge count is N−1 with natural subtraction. These satisfy O.05–O.07 for every N.
* **k=0:** when K>0 feasibility forces N=0. When K=0 the empty-family case allows arbitrary N. No arbitrary alphabet element or additional nonempty instance is chosen.
* **Zero selected prefix pile:** the occupied subset is empty for every permitted prefix array, by the proved zero-count property. All relevant formulas are zero without a legal-word premise.
* **Q=0:** O.05 and O.06 give zero collision expectation and O.07 gives zero edge expectation. Q is never inverted.

## Dependency and acceptance verdict

The new dependency order is acyclic: restricted count arrays → split equivalence → O.01; suffix restriction → O.02; split coordinates plus C.21 → O.03; trusted increasing enumeration plus C.37 → O.04; O.02/O.04 plus C.21/C.22/C.31/C.33/C.57/F12 → O.05; O.01/O.03/O.05 plus existing finite expectation calculus → O.06; O.06/F21/F02 → O.07.

I accept O.D01–O.D02 and all seven O statements, subject only to making the explicit N and count-array arguments match the current frozen core's signatures as described above. No mathematical correction, extra assumption, extra named helper, or existing-contract edit is required. This closes a finite occupancy-conditioning dependency if implemented and verified; it leaves the endpoint, stable-profile, and arbitrary-exploration conditioning obligations outstanding.

## Final signature and module comparison

I have now compared the complete `conditional_contract_statements.md` with this independent reconstruction. I accept all three exact definitions and all seven exact theorem signatures and conclusions without remaining pre-freeze issues. The report resolves the explicit-N and count-array conventions: N is explicit in `splitMatrix` and O.02; O.01 and O.05–O.07 infer it from the original count-sum proof; O.03 infers it from its actual matrix samples; O.04 remains a theorem about an arbitrary finite subset of natural numbers. The pure restrictions and deterministic identities carry no unused feasibility assumptions. O.01 allows arbitrary real f, and O.06–O.07 quantify over every natural q without requiring a nonnull slice.

The required literal restriction forward map of `splitMatrix` agrees with the reconstruction and supports the local projection proofs in O.03/O.05. The statement report explicitly preserves original label identities, the full-row/suffix-row equivalence for two occupied labels, the original N(N−1) factors, the sorted occupancy indicator, and the distinction between collision equality and the adjacent-edge inequality. Its empty-size, zero-pile, zero-tail, and null-event cases agree with the above audit.

The four-module order `Conditional.Model` → `Conditional.Split` → `Conditional.Counts` → `Conditional.Estimates` is acyclic and makes every dependency available without importing any unproved interface. O.05 does not mathematically need O.01, although the shared Split-module import is harmless. The allocation contains exactly three definitions and seven named theorems, with no additional custom instances or named helper declarations. This acceptance authorizes no implementation before the root records the new freeze.
