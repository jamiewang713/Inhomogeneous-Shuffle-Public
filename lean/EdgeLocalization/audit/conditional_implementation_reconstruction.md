# Independent implementation review of the conditional model and counts

I reviewed the complete actual `Conditional/Model.lean` and `Conditional/Counts.lean` against `audit/frozen_conditional_contract.md`. I accept the three definitions O.D01–O.D02 and the two theorems O.04–O.05. Their signatures, conclusions, and mathematical content match the freeze. I found no added hypothesis, extra named helper or instance, placeholder, or mathematical defect. This is independent of my implementation of `Conditional/Split.lean`.

## Literal split model

`Model.lean` has exactly `prefixCounts`, `suffixCounts`, and `splitMatrix` (lines 8–66). The restriction definitions retain the prescribed indices, use natural suffix length K−M, and do not acquire N or feasibility premises. The equivalence takes explicit N and its forward map is literally the pair of column restrictions at j and M+j (lines 19–21).

The inverse explicitly splits at j<M and uses j−M on the other branch. Reconstructing the selected column subtype from its existing value and proved histogram does not change its assignment; it supplies the required count-index transport. The suffix index equality is proved from M≤j. Both inverse laws are proved coordinatewise, including the index-bound arithmetic, with no assumed bijectivity or additional data. The construction remains meaningful for empty coordinate families and infeasible count arrays; it does not require choosing a sample or an alphabet digit.

## O.04: arbitrary occupied-label pair count

`increasing_pairs_in_finset_card` has exactly the single arbitrary argument `s : Finset ℕ`. Its proof transports increasing pairs through the trusted increasing order isomorphism from `Fin s.card` to s, and applies the existing `increasing_pair_card` (Counts lines 7–43). Membership, injectivity, and surjectivity are proved locally. Strict order is preserved in both directions, so each unordered pair is counted once. The argument covers empty and singleton s without an added nonempty premise.

## O.05: fixed prefix, original population

`tail_expected_collisionPairs_given_prefix_array` retains every frozen parameter, the original suffix matrix law, the sorted full-deck collision cardinality on the left, and `choose(prefix occupancy,2) * tailCollisionFactor N n M` on the right (Counts lines 46–56). All suffix column totals are derived directly from the original `hn`; they remain equal to N.

The N=0 and N=1 cases are resolved before any two-label probability theorem (lines 58–68). The latter uses occupancy≤1 to prove its binomial coefficient is zero. Thus no probability formula for a nonexistent distinct pair is invoked, and no zero denominator is cancelled.

In the remaining proof, s is the occupied subset of original labels determined solely by the fixed prefix array p (lines 69–79). It does not depend on the tail sample. The local prefix and suffix column equalities come from coordinate projections of `splitMatrix.apply_symm_apply` (lines 80–87). The proof then establishes pointwise prefix membership equivalence (lines 88–94), rather than inferring it from O.03's cardinal equality.

For two occupied labels, the local full-row equality equivalence with tail-row equality is correct in both directions (lines 95–119). The forward direction restricts full equality to suffix coordinates. The reverse direction splits each full coordinate at j<M: both entries equal the corresponding digit of x in the prefix branch, and the given tail equality applies after subtracting M in the suffix branch. The reconstructed full index is explicitly proved equal to j.

Every full collision pair lies in the deterministic increasing-pair set of s (lines 123–138). In particular, equality of the full rows transfers the prefix property from the first endpoint to the second, and the pointwise prefix equivalence returns both labels to s. For a pair already in s, lines 139–172 prove the exact event equivalence with suffix-row equality and derive distinctness from its strict natural ordering.

The invoked suffix theorem is the existing `matrix_pair_prefix_probability` with the empty prefix and the original population N. The empty prefix factor is one, and O.02 identifies the suffix product with the original absolute-index tail factor. Hence its numerical factors retain N(N−1); neither the sample law nor its denominators are replaced by the occupied count. There is no reciprocal occupancy or tail factor.

Finally, samplewise sorted/raw collision-cardinality invariance, F12, and O.04 give the stated expectation (lines 173–186). The argument asserts no invariance of individual edge locations and needs no independence of the sorting permutation. An empty or singleton occupied set contributes an empty pair sum; zero prefix piles and zero tail factors are covered without exclusions. Empty prefixes, empty suffixes, and repeated row words retain the existing model conventions.

## Scope and verification boundary

The declaration scan found exactly the three frozen definitions and O.04–O.05, with no additional named declarations or forbidden proof placeholders. Root and the implementing agents reported clean compilation of both modules. I performed the independent source and contract review recorded here, without rerunning their builds. This review does not claim a result about arbitrary exploration conditioning or the later O.06–O.07 implementation. No implementation or frozen file was modified.
