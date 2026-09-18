# Final statement and mathematical review of the exponent implementation

Reviewer: statements agent. I read the actual definitions and all fifteen proof bodies in the four exponent modules, compared their domains and conclusions with `frozen_exponent_contract.md`, and inspected the successful verification record and printed declaration types. No implementation or earlier review was edited during this review.

**Verdict: accepted.** All five definitions and fifteen theorem statements retain the frozen signatures and source meanings. The mean-power identity, square-tail identity, density conversion, small-case coefficients, and terminal specialization are proved without an additional hypothesis or named helper.

## Reviewed versions and verification

The frozen contract has SHA-256 `7f3dcbd0c6e99538300bbfe307c2516440647ebd3999e28285439024c8b3a848`, recorded before implementation at 22:07:11 UTC.

| File | SHA-256 |
| --- | --- |
| `EdgeLocalization/Exponent/Model.lean` | `db39dbcc02675a03461380ce8afdbc2c798268285ceb52e9f2401fbd55869106` |
| `EdgeLocalization/Exponent/Mean.lean` | `81990e2b66d7904b76e1a50ee29e4bd77e02380db81520c9a0a36542c482c968` |
| `EdgeLocalization/Exponent/Tail.lean` | `d90467dc983d54befe7a75ec2e09cc147b0caf96f2311720e166324153fdf24d` |
| `EdgeLocalization/Exponent/Estimates.lean` | `9926b173940a45c43c50684311a7de2af938917338f96a9c60b88a75e0d75bd3` |

These independently read source hashes match `exponent_verification.json`, whose successful run is dated `2026-09-17T22:11:38.346165+00:00`. Root also confirmed that `python3 verify_exponent.py` passed and that Estimates compiles with default limits. The verification used Lean 4.24.0 and mathlib revision `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

The verifier records exactly fifteen theorem declarations and five definitions, no prohibited proof tokens, and unchanged mathematical sources, parent implementations, frozen contracts, and prior independent reviews. I compared the printed signatures and actual declaration bodies with the contract rather than treating a successful build or matching names alone as a signature check.

The axioms report shows that `legalPrefix_of_prefix` and `legalPrefix` use no axioms. All other audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`. There is no new custom axiom, assumed logarithmic identity, or placeholder theorem.

## The five definitions retain the source meanings

`Model.lean:11` defines legality by positivity of the selected natural count at every prefix index. It adds neither population data nor feasibility to this predicate.

`Model.lean:15` defines the ambient size exponent as the original real parameter `b` minus the actual extension log costs divided by `log N`. Its filter `A ≤ t.val` on `Fin M` selects precisely the one-based source columns `A < j ≤ M`. Each logarithm uses real division of cast counts. It does not use the mean to define the exponent.

`Model.lean:20` separately defines the signed ambient discrepancy as `log(prefixMean w)/log N-b`. `Model.lean:24` defines the one-column pressure value as minus the log of the sum of squared proportions, and `Model.lean:27` defines the source tail exponent with the correct outer minus sign and the existing absolute tail-index filter.

The explicit/implicit argument conventions match X.D01–05. No structure field stores a desired estimate, positivity condition, rate, or power identity.

## Review of all fifteen statements and proofs

| ID and declaration | Domain and proof review |
| --- | --- |
| **X.01** `legalPrefix_of_prefix` — `Mean.lean:9` | Uses only `hM`, `hAM`, the two words, their pointwise extension equality, and legality of `x`. Composed column embeddings have the same value, and specializing `hx` proves ambient legality. No `N`, `hn`, or separately supplied legality of `w` appears. |
| **X.02** `prefixMean_pos_of_legal` — `Mean.lean:18` | Keeps explicit `N≥2`, source legality, and no count-sum premise. Positivity of every selected ratio is derived from the natural count inequality and positive real cast of `N`; finite product positivity proves the mean is positive. Empty products remain covered. |
| **X.03** `log_prefixMean_of_legal` — `Mean.lean:29` | The conclusion is the full-prefix actual-cost sum with the frozen sign. Both nonzero inputs of each use of `Real.log_div`, and nonzero product factors for `Real.log_prod`, are proved from legality and `N≥2`. There is no logarithm of a random realized occupancy and no imported factorization premise. |
| **X.04** `log_prefixMean_extension` — `Mean.lean:58` | Keeps exactly the pointwise prefix condition and legality of `x`, with no `b`, `hn`, or assumed mean ratio. A local `Finset.sum_bij` maps `Fin A` into the indices below `A`; injectivity, surjectivity onto that filtered set, and equality of the selected full-column costs are proved. The trusted filtered-sum partition and X.03 for both words yield the extension identity. No additional product-split declaration is used. |
| **X.05** `prefixMean_eq_rpow_ambientSizeExponent` — `Mean.lean:94` | `b` is an unrestricted real parameter. The local `hexponent` identity is proved by unfolding the two frozen definitions and using X.04; `b` cancels algebraically. Positive-base real-power expansion and `Real.exp_log` then give the mean identity. The code proves `log N≠0` from `N≥2` and mean positivity from X.02. It does not redefine `b` or assume the target identity. |
| **X.06** `column_square_sum_pos` — `Tail.lean:10` | The count sum equals `N`, with `N≥2`. The proof derives a positive count by showing that otherwise every natural count and hence their sum is zero. One positive square and nonnegative remaining squares prove the claim. No chosen positive digit or nonempty-alphabet hypothesis is added. |
| **X.07** `tailSquareFactor_eq_rpow_tailEdgeExponent` — `Tail.lean:28` | Retains arbitrary natural `M`, feasible original-`N` counts, and `N≥2`, with no prefix legality or `M≤K` restriction. Each square sum and the tail product are proved positive. The product-log identity and the two negations in the source pressure sum yield exactly `log(tailSquareFactor)/log N`; exponentiation proves the equality. The empty tail is included. |
| **X.08** `tailCollisionFactor_le_rpow_tailEdgeExponent` — `Tail.lean:58` | Has the same frozen domain as X.07. It composes the existing without-replacement tail comparison with X.07. The conclusion remains an inequality for the possibly zero fixed-count factor, not an equality. |
| **X.09** `matrix_internal_density_le_ambient_tail_exponent` — `Estimates.lean:9` | Retains exactly the original matrix feasibility, length and extension data, `N≥2`, and legality of `x`. It starts from the proved mean-fourth/tail-square density bound. Existing nonnegativity and X.08 justify squaring the tail inequality. X.05 rewrites the mean, and trusted real-power laws combine the exponents. The conclusion is exactly `N^(4*(L+ε)+2*E)/4`, with no spatial factor or discarded error. |
| **X.10** `matrix_internal_density_le_small_coarse_exponent` — `Estimates.lean:56` | Appends only arbitrary real `δ` and the frozen cutoff `L<2δ`. Base monotonicity follows from `N≥2`; the exponent comparison uses only `hsmall`. The final exponent is exactly `2*E+8*δ+4*ε`, divided by four. The cutoff is not changed to one involving `L+ε`. |
| **X.11** `matrix_internal_density_le_small_singleton_exponent` — `Estimates.lean:76` | Has the same domain and cutoff as X.10, without a stable-family premise. Its exponent comparison is `4L≤2L+4δ`; the result retains `2*L+2*E+4*δ+4*ε` and the denominator four. The theorem supplies the stated numerical form for every small legal prefix, without asserting singleton classification. |
| **X.12** `matrix_internal_density_le_ambient_size_exponent` — `Estimates.lean:97` | Retains the shared matrix signature with no smallness condition. The already proved density-to-mean estimate followed by X.05 gives exactly `D≤N^(L+ε)`. No conditional or spatial premise is introduced. |
| **X.13** `tailEdgeExponent_at_full_length` — `Tail.lean:66` | Keeps arbitrary `N` and `n`, with no feasibility or log-domain restriction. Each `j:Fin K` contradicts `K≤j.val`, so the tail filter is empty. The zero numerator gives the frozen exact equality `E(K)=0`. This is a total-function empty-sum identity, not a log-base interpretation at `N=0/1`. |
| **X.14** `matrix_internal_density_terminal_exponent` — `Estimates.lean:109` | Uses the frozen full-length word type `Fin K→Fin k` and the ambient bound `hA:A≤K`. It specializes X.12 at `M=K`; the required equality of length-bound proof terms is handled definitionally/proof-irrelevantly. There is no small-mean, singleton, or positive-tail hypothesis. Together with X.13 it gives the exact terminal numerical conclusion. |
| **X.15** `ambientMeanError_root` — `Mean.lean:121` | Keeps the frozen empty-word domain, `b=1`, `N≥2`, and no `hn` or legality premise. Empty-prefix mean is `N`, and the proved nonzero `log N` gives zero discrepancy. It does not impose this root cancellation on nonempty ambient prefixes. |

## Boundary conditions and interpretation

The positivity used by the proof is derived, not inserted as a later premise. Mean positivity follows from source legality and `N≥2`; ambient legality follows from pointwise prefix extension; tail square positivity follows from feasibility. The logarithmic conversion deliberately excludes `N=0/1`, while all earlier finite bounds remain unchanged. The purely empty-tail X.13 still quantifies over all populations.

The local sum and product arguments include empty prefixes, `A=0`, `A=M`, `M=K`, `K=0`, and empty tail filters. An empty alphabet with a present feasible column contradicts `N≥2` through the stated count sum; no alphabet inhabitance is assumed. Zero unselected piles and selected piles of size one remain permitted. The fixed-count tail factor may vanish; its logarithm is never taken.

Both `b` and the computed ambient error retain unrestricted signs. The two small-case theorems retain arbitrary real `δ` subject only to their displayed cutoff. All error coefficients and constants are unchanged: the fourth-power and both small-case bounds carry four copies of the ambient error, while the direct and terminal mean bounds carry one. No error is replaced by an asymptotic term or absorbed into another parameter.

The proof uses the original full matrix law and population throughout. The density remains the existing sum over absolute sorted-deck positions. No realized ambient occupancy, adaptive prefix, exploration-conditioned distribution, random-cut mixture, or relative-coordinate translation is introduced.

## Proof-only elaboration changes and final acceptance

The final Estimates proof explicitly obtains mean nonnegativity from the frozen proved positivity theorem before multiplying an inequality. Its uses of `change` expose the definitionally identical real-power notation expected by the trusted power lemmas. The corresponding mean proof also exposes that notation before expanding a real power. These are proof elaboration steps; they add no statement assumption or new mathematical estimate.

The four modules contain only the five planned definitions and fifteen planned theorems. All other reasoning is local within those declarations. The final verified version is accepted without a remaining signature, mathematical-domain, or dependency issue.

This acceptance certifies the exact finite exponent conversion and its stated absolute-coordinate consequences. It does not certify the source's missing negative-`c_F` spatial gains, stable-family classification, ambient recentering bridge, concentration results, or full upper/lower/random-pile proof.
