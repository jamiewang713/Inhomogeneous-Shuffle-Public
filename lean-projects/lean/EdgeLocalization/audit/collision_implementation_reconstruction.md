# Independent review of the sorting and final collision estimates

I compared the actual `Collision/Rows.lean` and `Collision/Estimates.lean` with `audit/frozen_collision_contract.md`, including the final signature policy in sections 8–9. This review is independent of my implementation of `Collision/Column.lean`. I accept the definition and statement fidelity of the reviewed declarations. I found no mathematical defect or added assumption.

## Sorting and count invariance

`Rows.lean` contains exactly C.D09–C.D11, C.18–C.31 (including both C.20 adapters), C.36–C.37, and C.48–C.49. Its prefix and row adapters retain the frozen lengths, alphabet, initial-segment embedding, and empty value outside the deck (lines 12–69). The representation theorem assumes only the stated alphabet membership; it does not add positive pile counts.

The merge-sort definition uses the frozen lexicographic comparison. The direction of `sortPermutation` is correct: sorted position maps to original row label. Its domain cast uses the symmetric length equality, followed by the trusted index-to-label equivalence (lines 72–115). The sortedness proof derives totality and transitivity from the order on row words. It does not assume that unequal labels have unequal row words, or require antisymmetry of the relation on labels. Thus ties and the empty deck are covered.

The collision-pair bijection explicitly orients the image pair by its minimum and maximum (lines 143–215). Injectivity excludes equal image labels. In the reversed case, the new first row is the old second row; `hpEq ▸ hpX` correctly transports the prefix condition to it, and `hpEq.symm` supplies the reversed equality. The inverse orientation splits on image order and uses the original strict ordering. This proves cardinality invariance, without claiming that adjacency or a fixed edge position is invariant under sorting. The samplewise sorting permutation may depend on the matrix: C.30–C.31 require no independence or distributional assumption about it.

The increasing-pair count is exactly `Nat.choose N 2`, including N = 0 and N = 1. C.48–C.49 separately prove that those deck sizes have no collision pairs (lines 232–270). All auxiliary constructions in these proofs are local; no unreviewed named helper theorem or definition was introduced.

## Final internal-edge estimates

`Estimates.lean` contains exactly C.47 and C.50–C.55, with the frozen universal parameters and conclusions. C.47 uses the sum of edge probabilities equal to the expected edge count and nonnegativity to bound the sum of their squares by the square of their sum (lines 12–26). This is the square of the expected edge count, not the expected square of the count.

C.50 retains the tight coefficient `(N - 1)/(2N)`, with natural subtraction before casting (lines 28–59). The proof first handles N = 0 and N = 1 by the exact collision expectation formula. Only the remaining N ≥ 2 branch invokes the two-label factor inequality and clears a nonzero denominator. The identity with `Nat.choose N 2` and the substitution `prefixMean = N * prefixMass` give precisely the frozen coefficient. C.51 bounds it by 1/2, explicitly handling N = 0 and checking the multiplied factors are nonnegative (lines 61–87). No positivity assumption on N is exported into these statements.

C.52 uses the previously frozen injection bound from adjacent internal edges to unordered identical-row pairs. C.53–C.54 establish nonnegativity of the expected edge count before squaring the upper bound. The resulting coefficient in C.54 is exactly 1/4, giving the frozen bound `prefixMean^4 * tailCollisionFactor^2 / 4` (lines 89–136). C.55 combines the previously frozen density-to-occupancy bound with the exact sorted occupancy expectation (lines 138–150).

These conclusions preserve the original fixed-count product law, whole population N, and absolute sorted edge positions. They add neither a small-block assumption nor a smoothing factor involving cF. They therefore prove the reviewed finite internal-edge consequences; they do not assert the stronger source localization or anti-concentration claims, or a conditional exploration theorem.

## Verification boundary

This is a source-level mathematical and contract review. During the review, the root agent reported that `Collision/Estimates.lean` compiled with all seven assigned frozen theorems and the completed Matrix dependencies. I did not rerun that build or inspect the full 58-theorem verifier result. No implementation, source manuscript, or frozen contract was modified by this review.
