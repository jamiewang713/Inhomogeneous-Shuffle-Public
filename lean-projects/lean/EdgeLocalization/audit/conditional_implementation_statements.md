# Independent implementation review: split and occupancy-slice statements

This is a static review of `Conditional/Split.lean` and `Conditional/Estimates.lean` against the frozen conditional contract. I read both files in full and checked O.01–O.03 and O.06–O.07 against their frozen domains, formulas, and permitted proof dependencies. I did not edit any implementation, source file, prior review, or frozen contract.

Reviewed source fingerprints:

- `Conditional/Split.lean`: `ae25208eab9afd983de656c9dad501baf1cd0744da7829d6ad93b93517b4a989`.
- `Conditional/Estimates.lean`: `f968dc0dd3cbe0b9e8fc0be57c1d0b9c3715daf3dd7ee1de23efbc6802314a79`.
- Frozen conditional contract: `0790d840b1e1fc25f496672fedf6c68a6e76b99961e0173e6478cc0761e71689`.

**Verdict:** the reviewed definitions of observables, theorem statements, and mathematical proof steps conform to the frozen contract. I found no strengthened hypothesis, weakened conclusion, population change, indicator mismatch, or extra named helper. This static review does not claim that the dependent `Counts.lean` proof or the final `Estimates.lean` build has already been verified; O.05 was still being implemented when this review was requested.

## O.01: arbitrary real finite Fubini

`Split.lean:12–20` preserves the full frozen domain, including arbitrary `f : FixedMatrix N n → ℝ`. There is no sign, integrability, cardinality-positivity, or event-probability premise.

The prefix and suffix count proofs at lines 24–26 are inherited by applying `hn` at the actual restricted indices. Both component matrix laws retain population `N`; no normalization by prefix occupancy occurs.

The split-space cardinality identity at lines 28–30 is proved from the actual `splitMatrix` equivalence and the trusted product cardinality identity. The weight identity at lines 31–34 is then proved from existing C.17 for all three constructed laws. Uniformity or independence is not introduced as a local assumed interface.

The remaining argument reindexes the finite sum through that equivalence, uses the product-type sum identity, and distributes the proved product weight. Ring algebra works for arbitrary real `f`. Empty coordinate arrays and zero/one-card populations remain in the quantified domain, and there is no cancellation of an unsupported positive denominator.

## O.02: exact suffix factor and original population

`Split.lean:55–80` has exactly the pure factor signature: explicit `N`, the count array, and `hM`, with no `hn` or `N≥2` premise. Its forward index map is `j ↦ M+j.val`; its inverse on the suffix finset subtracts `M`. The membership, injectivity, and surjectivity goals are proved explicitly.

The summand identity is definitional from `suffixCounts`, so neither counts nor population are changed. At `M=K` the bijection relates two empty finite index sets; both products remain one. Total arithmetic at `N=0,1` is only algebraic here and is not misused as a probability for nonexistent distinct labels.

## O.03: prefix membership before cardinality

`Split.lean:82–111` has the frozen deterministic signature, with actual prefix/tail arrays and no `hn` premise. The proof first obtains the glued prefix-coordinate equality from `splitMatrix.apply_symm_apply` (lines 90–95).

It then proves a pointwise prefix-membership equivalence for each `i : Fin N` using C.21 twice (lines 96–103). Only after that does it prove equality of occupied finite sets and their cardinalities. The natural-index extension is handled by the explicit `i<N` and outside-range cases at lines 107–111.

Thus this proof does not infer membership from cardinal equality. The additional full-row/tail-row equivalence required by O.05 remains a separate local obligation in `Counts.lean`, as required by the freeze.

## O.06: the same sorted occupancy on both sides

`Estimates.lean:9–17` preserves exactly the frozen theorem parameters and statement. The indicator on the left is the **sorted full-deck occupancy**, and the probability on the right uses that same sorted occupancy. The collision count also uses the sorted full deck. The coefficient is `(Nat.choose q 2 : ℝ) * tailCollisionFactor N n M`.

The local `z` at lines 29–30 is this sorted observable. The local `zp` at lines 31–32 is raw occupancy in the prefix array. Their relationship is proved at lines 33–36 by composing the already verified sorting-cardinality identity with O.03. The code does not silently redefine the source observable as raw-prefix occupancy.

The inherited prefix/suffix count proofs at lines 21–24 only apply the original `hn` at the corresponding index maps. The suffix still has a law on `N` labels. The actual matrix split theorem is applied at lines 37–40 to arbitrary real integrands.

The probability bridge at lines 41–48 applies O.01 to the indicator and uses normalization of the inner tail law. This proves the probability identity needed later; it does not posit conditional independence of the prefix columns after fixing occupancy.

The inner expectation at lines 49–62 splits explicitly on `zp p=q`. On the true branch it uses the frozen O.05 formula and substitutes `q` for `zp p`. On the false branch its integrand and expectation are zero. The final finite-sum algebra extracts the fixed coefficient and rewrites the prefix-law event probability back to the original sorted-occupancy probability.

No step divides by that probability. Consequently a null slice, an impossible value `q>N`, or a zero tail factor does not require a new premise or a fabricated conditional distribution. The same algebra covers `q=0,1`; the corresponding pair coefficient is zero. The `N=0,1` collision facts are inherited through O.05 rather than bypassed with an illegal two-label call here.

## O.07: adjacent edges remain an inequality

`Estimates.lean:82–101` has the same unrestricted parameters and the same sorted occupancy indicator as O.06. It compares the edge-slice integrand with the collision-slice integrand pointwise.

On the true branch, frozen F21 supplies the natural cardinality inequality, which is cast to reals. On the false branch both quantities are zero. Existing expectation monotonicity and O.06 finish the argument. No equality between adjacent edges and unordered collision pairs is asserted, and there is no assumption on edge locations or on the sorting permutation's law.

## Declaration and scope check

The two reviewed files contain exactly the five assigned named theorems: O.01–O.03 and O.06–O.07. Their other abbreviations and helper facts are local proved steps explicitly permitted by the freeze. No new probability law, named theorem, custom instance, `axiom`, `sorry`, or `admit` appears in the reviewed files.

Static acceptance is limited to these reviewed file versions and their conformity with the frozen finite occupancy-slice contract. Final kernel checking must still include O.05 and the dependent estimates, and the resulting axiom reports. These finite slice statements do not claim endpoint localization, a residual model under arbitrary exploration, or the printed spatial `−c_F` gain.
