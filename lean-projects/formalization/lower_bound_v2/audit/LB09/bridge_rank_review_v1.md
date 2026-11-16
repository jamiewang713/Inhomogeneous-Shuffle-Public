# LB09 independent words, bridge and rank-barrier review v1

Date: 2026-10-01. Reviewer: LB09 mathematical-review/Geometry worker, independent of the three reviewed implementations. Reviewed files are `RiffleLowerV2/Localization/{Words,Bridge,RankBarriers}.lean`. No reviewed file was modified.

## Verdict

Approved. No substantive mathematical error, missing hypothesis, representation mismatch, fixed-factor omission, or tail-dependent event was found. The rank membership conclusion retains the actual integer cold set and random ambient translation. The deterministic helper premises still need the actual simultaneous concentration event in final assembly; these files do not claim that probability result.

## Mathematical checks

Words: the chronological column sets split exactly at ms, mu and mu+bridgeLength. The relevant product factorizations require ms≤mu and mu+bridgeLength≤K, so `prefixAt` does not silently truncate a required block. The actual join recovers each supplied selected coordinate map. Concatenation is injective in prefix/tail data with fixed bridge, and the full-family cardinality therefore equals the product of class cardinalities. `reservePrefix_mean` includes precisely ambient, selected-prefix and bridge factors; it does not include any tail factor. `joinColdWord_mass` includes all four blocks. Canonical ambient mass uses the empirical grid sum and the actual maximizing digit, yielding exactly `N^beta(s)` rather than an asymptotic proxy. Empty prefix and tail blocks remain valid.

Bridge: `goodColumn_ordered_digits` (lines 9–15) orders two distinct good digits without changing either probability guarantee. `exists_bridgeGeometry` (lines 87–175) uses two distinct ordered good columns from WitnessSpec. Its central word uses the large good digit at the first and the small good digit at the second, with canonical maximizing digits elsewhere. Each reserve is a single Function.update of this central word. Thus the minus reserve retains the central right good digit and the plus reserve retains the central left good digit; neither is incorrectly treated as maximizing at that unchanged distinguished column.

The product lemma at Bridge:17–48 gives the conservative lower mass `chi^2*k^(-bridgeLength)` by putting an extra factor 1/k even at each distinguished column. This is valid for k≥1 and does not lose either good-digit factor. Bridge:50–84 handles the ceil-length cost and gives the exact finite logarithmic upper bound containing `(log k+2log(1/chi))/log N`. Positivity of the central mass and its upper bound by one are checked before using logarithms. The exported per-coordinate floor applies to all three words.

RankBarriers: `take_lt_split` and `take_le_split` (lines 40–91) faithfully split a comparison into an earlier-prefix difference or equal ambient prefixes followed by a suffix comparison. `relative_rank_decomposition` (lines 109–141) consequently has the same `lowerRank(prefixAt l a)` translation for both the lower and upper relative endpoints. This matters: replacing the right translation by the ambient upper rank would be wrong, and the implementation does not do so.

The sorted prefix comparisons (lines 143–212) reindex actual row counts by the sorting permutation. The central and both reserve words have identical prefixes up to mu; strict bridge comparison is independent of all later digits (lines 214–241). The resulting barriers (lines 243–291) are

`q + Lrel + Cminus <= i.val`,

`i.val + 1 + Cplus <= q + Urel`.

These are exactly the manuscript's one-based barriers after setting rank=i.val+1. Prefix counts of the reserves include every possible tail completion, which is the required reserve population.

## Representation and event checks

`coldWord_mem_translate` (lines 293–327) converts to the literal shared `clipTranslate` definition via `manuscriptRank i-q`, with `manuscriptRank i=i.val+1`. It then uses the actual selected interval in the `coldRelativeSet` biUnion. The absolute endpoint bounds and counts at least e+2 imply the weak left and strict right inequalities of `[ell,r)`. The right endpoint is not accidentally closed. The two-unit slack is retained explicitly in the theorem premises and arithmetic.

The helper quantifies over an arbitrary tail z, without a tail-class membership premise. `coldFamily_localized_of_endpoint_reserves` (lines 329–354) fixes one sample omega and one set of bounds indexed only by selected prefixes x; it then concludes localization for every selected full word and every occurrence. No new event is selected for z. There is no independence premise involving tail columns, reserve counts, or the random ambient translation.

The words and bridge are deterministic data. Their existence proofs depend on cuts, WitnessSpec and type data, not omega. The finite rank lemmas work on an arbitrary fixed sample and do not introduce stochastic assumptions. Final Event assembly must supply their numerical premises from the actual all-prefix event.

## Reviewed source hashes

| Source | SHA-256 |
|---|---|
| Words.lean | f2ddc788402900b53cbcf979cd7185883502cd69deaab06457407aee7092afa6 |
| Bridge.lean | 2b40a62ac461c103525a152e414a5e92decc5ba7f8a36634a60ad461ac27194b |
| RankBarriers.lean | 354cbdde0d9f4a30ddc49f925dae211145369461d33d3cbbeeb71961cd759f75 |

Words and Bridge were recompiled as dependencies of the successfully checked Geometry target. The RankBarriers source was reviewed as its worker completed the final membership build. The lane's final compiled audit should independently confirm the exact current sources and standard axiom closure.
