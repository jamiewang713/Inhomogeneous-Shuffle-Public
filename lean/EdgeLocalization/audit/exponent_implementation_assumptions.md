# Independent implementation audit: exponent model and mean

I independently compared the current `Exponent/Model.lean` and `Exponent/Mean.lean` with `frozen_exponent_contract.md`, inspected all definition and proof bodies, rebuilt the Mean module, and checked the compiled signatures and axiom dependencies. I changed no proof, definition, mathematical source, contract, or hashed review.

**Verdict: accepted. X.D01–X.D05, X.01–X.05, and X.15 retain their exact frozen statements and meanings, with no added assumption or hidden helper.**

## Definition fidelity

The five Model declarations match the frozen argument orders and literal formulas. `legalPrefix` refers only to positive selected actual counts, with the original `Fin.castLE` column inclusion. `ambientSizeExponent` remains b minus the actual suffix log-cost sum divided by log N. Its filter selects `A≤t.val` within `Fin M`, exactly the source's one-based times A<j≤M. It is not defined through `prefixMean` or through a presumed power identity.

`ambientMeanError` is computed as log(prefixMean(w))/log N−b, retaining its unrestricted sign. It is neither a rate assumption nor a positive error allowance. `columnPsiTwo` uses the squared actual proportions and a negative logarithm; `tailEdgeExponent` uses the matching tail filter and the source's additional outer minus sign. The numeric divisions in the log costs are real divisions of cast natural counts. None of the definitions inserts feasibility, legality, asymptotic rates, or positivity premises into its data.

## Proof and statement fidelity

- **X.01:** ambient legality is derived by applying x's legality at the included ambient coordinate, rewriting the selected digit by the explicit extension equality, and using the definitionally equal composed column inclusion. There is no separately assumed legality of w, ambient length bound, or count-sum premise.
- **X.02:** positivity of the mean is proved from N≥2 and the selected positive counts. The product proof works for an empty prefix and requires neither feasibility nor a positive alphabet-size hypothesis.
- **X.03:** the complete log-mean formula is proved from the actual prefix product. The proof first derives positive real selected counts and ratios, then justifies `Real.log_mul` and `Real.log_prod` with their nonzero conditions. Both `log(n/N)` and `log(N/n)` use real cast division; their negative relation is proved termwise with `Real.log_div`. No logarithmic factorization or mean formula is assumed.
- **X.04:** the extension identity is a genuine finite initial-segment argument. Its local `Finset.sum_bij` maps `Fin A` to the filtered `Fin M` indices with value below A. It proves target membership, injectivity via values, surjectivity using the target's proved bound, and equality of summands using the original digit-extension hypothesis. The complementary filter is exactly `A≤t.val`. The proof then applies the two already proved full-prefix logarithmic identities, deriving w's legality by X.01, and rearranges the exact sum split. No element of an empty prefix is chosen and no cardinality or sum identity is an extra premise.
- **X.05:** the proof locally derives `L+ε=log μ_x/log N` from the unchanged definitions and X.04. The arbitrary b cancels algebraically; it is never reset to log μ_w/log N. It proves log N≠0 from N≥2 and μ_x>0 from X.02 before applying trusted real-power and exponential/logarithm identities. The local change from explicit `Real.rpow` to power notation is definitional equality and changes no statement. There is no sign assumption on b, L, or ε and no feasibility premise.
- **X.15:** the empty-prefix product gives the exact mean N. The proof derives log N≠0 from the stated domain and simplifies log N/log N−1 to zero. The conclusion is precisely the frozen b=1 root normalization, with no unused feasibility or legality hypothesis.

The Mean file contains exactly the six frozen theorems, and the Model file exactly the five frozen definitions. All auxiliary functions, positivity facts, finite sum identities, and scalar cancellations are local proved steps. There are no extra named lemmas, abbreviations, instances, or hidden section parameters.

## Boundary cases and scope

The proofs cover A=0, M=0, A=M, and K=0 through the existing empty sums/products and the explicit finite bijection. In the equal-length case the complementary suffix sum is empty; no assumption equates the ambient mean to N^b. Legal selected piles of size one are permitted, and unselected piles can be zero. Illegal selected zero counts are excluded exactly by `legalPrefix`, rather than by an additional lower-bound hypothesis.

The absence of hn in the pure mean identities is deliberate and correct: they are algebraic statements about the selected positive ratios, even for arrays that are not feasible matrix count arrays. Actual-matrix statements elsewhere retain feasibility before interpreting this numeric mean as an expectation. Empty alphabet cases introduce no inhabitance requirement; empty prefix functions still exist, and a nonempty legal digit prefix itself supplies the required digits.

N=0 and N=1 remain outside these logarithmic conversion theorems' explicit N≥2 domain. The total definitions do not claim to give the source's base-N logarithm meaning there. The exact ambient discrepancy remains deterministic and signed, and no convergence rate is inferred. Neither file changes edge coordinates, conditions on a realized ambient occupancy, or replaces the original population N by a residual size.

## Verification evidence

My independent `lake build EdgeLocalization.Exponent.Mean` completed successfully. A separate Lean import checked all five definition signatures and all six Mean theorem signatures. `#print axioms` reported no axioms for `legalPrefix` and X.01, and only `propext`, `Classical.choice`, and `Quot.sound` for the other reviewed declarations. The source scan found no `axiom`, `sorry`, `admit`, unsafe declaration, or unproved placeholder.

The root additionally reported that the complete exponent verifier passed all five definitions and all fifteen statements, including the current Estimates module, at default limits. It also verified unchanged mathematical-source, parent-module, and review hashes and only trusted foundational dependencies. That complete-verifier result is separate from my independent source, signature, build, and axiom review of Model and Mean above.

These accepted files establish the exact finite mean conversion and preserve the source exponent definition. They do not by themselves establish an ambient error rate, a relative-coordinate density identity, the printed spatial saving, or the remaining stable-block and first-moment arguments.
