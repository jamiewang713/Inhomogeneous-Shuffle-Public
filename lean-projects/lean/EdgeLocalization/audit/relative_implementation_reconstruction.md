# Independent review of relative density and exponent implementations

## Scope and verdict

I independently read the complete implementations of `Relative/Density.lean` and `Relative/Estimates.lean` and compared all R.08–R.18 signatures and proof bodies with `frozen_relative_contract.md`. **The reviewed code preserves the exact frozen domains and conclusions. I found no mathematical defect, added assumption, unproved interface, extra named declaration, or density-invariance claim.** No reviewed implementation or frozen artifact was edited.

Reviewed hashes:

- Density.lean: `774163841c68a9da6de8f5f0a27c1d03a09c18302b7e251a1e4625acbab93637`.
- Estimates.lean: `10df361c6a48b88bad4595aca97460eedd86af9b9c62f052ec52e932de348a40`.
- Frozen relative contract: `e5c6977f4b448a62ddd54e64893016c2fbfa83c8a9ab34532590db3012fb73f4`.

This is an independent source and mathematical review. After the source comparison, the root confirmed that Density and Estimates both compiled cleanly at the default compiler settings. The root subsequently reported the full verifier passed at 22:32:25.732798 UTC: all eighteen frozen statements and three definitions matched, all twenty-one prior implementation modules and the source/contract/review hashes were unchanged, and axiom dependencies were confined to `propext`, `Classical.choice`, and `Quot.sound`. The root directly inspected the printed signatures, axiom lists, and verification record. That is root-reported verification; I did not rerun the full verifier. The separately authored Deck implementation was compiled and its axiom dependencies inspected in my implementation task; that is not an independent review of my own code.

## Relative/Density.lean

**R.08, lines 11–37.** The finite outcome type, existing law, row map, target list, and sample-dependent natural shift exactly match the frozen signature. The local random set H is the defined relative edge set, with its support proved by R.01. Existing F12 identifies the sum of its membership probabilities with expected relative cardinality. The pointwise translation injection R.03 gives domination by expected absolute edge count. The proof explicitly derives nonnegativity of the relative expectation; the upper expectation is then nonnegative by the same inequality. The squared-expectation comparison is therefore valid. The first step uses nonnegative membership probabilities to bound a sum of squares by the square of their sum. It never compares relative density with absolute density.

**R.09, lines 39–56.** The existing finite-law sum-of-squared-probabilities bound first bounds density by expected relative cardinality. R.03 and the already proved absolute-edge-to-occupancy bound are composed pointwise, then averaged. No shift independence, positive occupancy, sorting, or common row length is assumed. The expectation still counts xList occupancy in the original N-row deck.

**R.10, lines 58–62.** The only density equality with the absolute definition is the frozen constant-zero-shift case. It follows by unfolding both density definitions and applying R.02 to each outcome. No nonconstant translation is generalized from it.

**R.11, lines 64–76.** The existing constructed product law and expected finite-intersection theorem are applied to the same relative-set function on both copies. The displayed first set uses `R z.1` and `shift z.1`; the second uses `R z.2` and `shift z.2`. Thus the theorem compares equal relative positions after each independent sample's own recentering. It does not share a random shift, use the first sample's shift for both graphs, or couple the two samples diagonally. The only support premise is proved by R.01. Products of equal probabilities are correctly identified with squares.

**R.12, lines 78–94.** The actual-matrix signature retains the original feasibility proof, legal length bound, arbitrary vector x, and arbitrary shift, with no population lower bound or prefix-legality assumption. The proof uses R.08 and the previously proved expected absolute-edge bound. Nonnegativity of the expectation is derived from natural edge counts; its upper bound is nonnegative by transitivity. Squaring gives exactly the fourth power of the mean times the squared fixed-count tail factor divided by four. It does not import the absolute-density fourth-power conclusion as a bound on a different density. All original N denominators remain inside the unchanged numerical factors.

**R.13, lines 96–107.** R.09 and the proved exact sorted-occupancy expectation give the frozen mean bound. This also preserves the full all-N finite-matrix domain and arbitrary sample-dependent shift.

The six listed R.08–R.13 theorems are exactly the module's new declarations. All auxiliary sets, support facts, inequalities, and sign proofs are local. The existing product law and numerical factors are reused unchanged.

## Relative/Estimates.lean

**R.14, lines 9–57.** The statement retains exactly the frozen X.09 vector domain and its computed shift `ambientLeft N (sortedRows n omega) (prefixWord w)`. It keeps the original population and law and a deterministic ambient/child prefix pair. The proof starts from the new relative matrix bound R.12. The existing exact mean identity supplies the power with exponent L+epsilon, and the existing tail comparison bounds the possibly zero fixed-count tail factor by the positive square-tail power. Nonnegativity used before squaring is proved upstream, not supplied as a new premise.

The local fourth- and second-power conversions use trusted natural-cast and real-power multiplication identities with positivity of N derived from N≥2. The product becomes the real power with exponent `4*(L+epsilon)+2*E` by the real-power addition identity. The coefficient remains precisely 1/4. The calculation never redefines the source cL, discards the signed ambient discrepancy, takes a logarithm of a zero collision factor, or assumes equality of the fixed-count and square-tail products.

**R.15 and R.16, lines 59–100.** Both statements and proofs use the literal source branch condition `L<2*delta`. Their only scalar input to the linear comparisons is this `hsmall`; no sign of delta, L, E, b, or epsilon is used. Monotonicity at base at least one is derived from N≥2. The two conclusions retain exactly `2*E+8*delta+4*epsilon` and `2*L+2*E+4*delta+4*epsilon`, both divided by four. In particular the cutoff is not changed to one on L+epsilon, and the error coefficient does not drop from four to two. The singleton-shaped theorem contains no unimplemented singleton predicate or spatial saving.

**R.17, lines 102–114.** This uses R.13 at the actual ambient shift, followed by the already proved exact mean-power identity. It retains the exponent L+epsilon with no small-size premise or assumed mean bound.

**R.18, lines 116–127.** The terminal theorem is exactly the full-length specialization of R.17 and the frozen X.14 argument domain. The ambient bound proof agrees by proof irrelevance. There is no small-mean or new terminal-tail premise; the already proved X.13 supplies E=0 when the terminal statement is interpreted together with its tail exponent.

The five R.14–R.18 theorems are precisely the module's new declarations. There is no added exponent helper, definition, instance, assumed rate, or hypothesis.

## Cases and interpretation boundary

The probability and finite-matrix proofs retain N=0 and N=1, for which the fixed support is empty. Empty outcome atoms and zero weights cause no division by event probabilities. Arbitrary shifts can discard earlier edges, but the generic inequalities use only the valid cardinal domination. The separately proved actual-sorted prefix bridges R.06–R.07 establish that the canonical ambient shift retains all source child edges; these density proofs do not assume that fact or use it to infer density invariance.

Zero selected or tail pile counts remain allowed in the all-N matrix inequalities. The exponent wrappers impose only their previously frozen selected-prefix legality and N≥2 domain. Empty/equal/full-length prefixes, empty tail products, and either sign of the exact ambient discrepancy remain covered. The empty ambient yields zero shift by R.05 and hence the existing root density through R.10.

The resulting relative density has its precise independently recentered overlap meaning by R.11. None of these implementations identifies it with the pretranslation overlap, conditions on exploration data, changes the population, or selects an adaptive prefix. The exact finite small and terminal bounds are now statements about the intended ambient coordinates. The stronger minus-cF spatial estimates, localization/windows, and global first-moment aggregation remain outside these proved conclusions.
