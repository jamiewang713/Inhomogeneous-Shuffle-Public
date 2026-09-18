# Independent asymptotic implementation audit

I independently compared `Asymptotic/Model.lean` and `Asymptotic/Error.lean` with A.D01 and A.01–A.02 in `frozen_asymptotic_contract.md`. The freeze is dated 2026-09-17 22:44:36.787074 UTC, with contract SHA256 `659ee8a94a40e3c4cd7b607409d42297f0d0d41fe41c6414d9a3d9ca30aff8a8`. This review does not modify any implementation, mathematical source, frozen contract, or frozen review.

**Verdict: accepted for the two reviewed modules.** Their definitions, ordered parameters, hypotheses, quantifiers, and conclusions match the freeze. The proof uses only the frozen assumptions, earlier proved project statements, and trusted real logarithm and power results. No hidden positivity, ambient legality, profile rate, or independence hypothesis has been introduced.

## A.D01: exact size-exponent definition

`HasSizeExponent` is exactly the two-sided real-power sandwich for every positive accuracy, with a natural-number threshold quantified after that accuracy. It adds no global sign condition, monotonicity, logarithmic conclusion, or bound on the real exponent `b`. It remains total at populations zero and one. Its initial segment can contain zero or negative values for a generic scalar function, because the later witnesses may exclude any finite initial segment.

`Model.lean` has exactly this one definition and imports trusted real-power material. In particular, the definition has not been replaced by an assertion about logarithmic error or by a family structure containing desired conclusions.

## A.01: scalar logarithmic error

The implemented proof follows the frozen route in full. It applies the size hypothesis at the requested positive accuracy, obtains a cutoff `N1`, and chooses `max N1 2`. For every population beyond that cutoff, both `N1 ≤ N` and `2 ≤ N` are proved locally. Thus positivity of the real base and the strict inequality `1 < (N : ℝ)` are derived from the output domain; neither is an extra premise.

The lower real power is proved strictly positive for arbitrary real `b - ε`, using positivity of the base. Its comparison with `f N` then proves `0 < f N`. This occurs before the upper logarithm comparison. The proof therefore never relies on the totalized logarithm at zero or at a negative argument to establish a useful inequality. Negative exponents, functions tending to zero, and negative logarithm values are all covered by the same positive-argument argument.

Both bounds are transported through `Real.log_le_log` with the needed positivity proved explicitly. `Real.log_rpow` is applied only to the positive base. The two divisions use the independently proved strict positivity of `Real.log (N : ℝ)`, preserving inequality direction even when the numerators or exponent bounds are negative. The final two linear inequalities yield exactly the weak absolute-error conclusion `≤ ε` via `abs_le`; no smaller accuracy, stronger hypothesis, or assumed limit theorem is used.

There is no need to split `N=0` and `N=1` inside this eventual conclusion: the constructed witness excludes both, and that exclusion is present in the theorem's output. No claim about logarithmic error at an initial population is made. The condition `ε > 0` is exactly frozen; no conclusion for nonpositive accuracy is claimed.

## A.02: actual expectation to computed ambient error

The explicit parameter order is precisely `k`, `K`, `A`, `n`, `hn`, `hA`, `w`, `b`, `hsize`, `ε`, `hε`. The size hypothesis remains on the actual expected sorted occupancy under `matrixLaw (n N) (hn N)`, with the supplied ambient prefix `prefixWord (w N)`. It has not been moved to a product expression or to an independent-row law.

The proof applies A.01 to that exact expected-occupancy function and retains its threshold. At a population beyond the threshold, it rewrites using the previously proved `matrix_expected_sorted_occupancy (n N) (hn N) (hA N) (w N)`. The resulting expression is definitionally the existing `ambientMeanError`; the final `exact h` performs no additional mathematical identification. Thus the exact mean identity is proved project input, not an assumed interface, and the signed error definition is unchanged.

No ambient-legality or positive-mean premise has been added. The generic lower sandwich proves eventual positivity of the actual expectation when needed by A.01. The expectation-to-mean identity used by A.02 itself holds for all finite populations and prefixes under the already frozen feasibility data. Initial illegal ambient prefixes or zero expectations are therefore not silently ruled out. No conditioning on occupancy, nonnull event, or residual population is present.

The family data remain total on `ℕ`, including zero and one, but the asserted small-error domain begins at a proved threshold at least two. Empty prefixes, zero columns, empty alphabets when their existing data are consistent, and zero unselected pile sizes require no new case assumption. The child variables do not occur in A.02 at all, so this computed-error threshold depends only on the one supplied ambient family and the accuracy. It cannot establish a common threshold over an unrelated class of ambient families or exploration histories.

## Verification and preserved scope

- An independent `lake build EdgeLocalization.Asymptotic.Error` completed successfully at default limits.
- A fresh Lean import checked the elaborated types of A.D01 and both theorems. Their public parameters and conclusions match the frozen text.
- `#print axioms` for all three reviewed declarations returned only `propext`, `Classical.choice`, and `Quot.sound`.
- A declaration and forbidden-token scan found exactly one definition and the two frozen theorem names, with no extra named helper, instance, `axiom`, `sorry`, `admit`, `unsafe`, or proof-limit option.
- An independent SHA256 comparison checked 39 recorded objects: this contract, all parent contracts, all 25 parent implementation modules, the four frozen pre-reports, and the three permitted mathematical sources. Every recorded hash matched.

Reviewed implementation hashes are `920def79ccd1b8d88d233f1bd7b814358543353eed1440634358a77b3eec0b66` for `Asymptotic/Model.lean` and `0f119e3a9896944719fcd5c717bb9466c4fd30c7ceed5d9c1a97f4565a03533d` for `Asymptotic/Error.lean`.

This independent review covers A.D01 and A.01–A.02. It does not substitute for the separate review and whole-addendum verification of A.03–A.07. These scalar and expectation results convert exactly the source's ambient expected-size assumption into its computed error bound; they do not supply concentration, stable-family classification, uniformity over varying ambient families, the negative fluctuation-exponent saving, or the remaining global first-moment argument.
