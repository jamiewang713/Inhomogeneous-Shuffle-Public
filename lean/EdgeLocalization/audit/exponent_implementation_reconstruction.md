# Independent review of the tail and density exponent implementations

## Scope and verdict

I independently read `EdgeLocalization/Exponent/Tail.lean` and `EdgeLocalization/Exponent/Estimates.lean` against the exact frozen definition meanings and X.06–X.14 statements in `frozen_exponent_contract.md`. **Both reviewed modules preserve the frozen signatures and mathematical meanings. I found no added premise, changed conclusion, extra named helper, or mathematical defect.** I made no implementation or frozen-artifact edits.

Reviewed source hashes:

- Tail.lean: `d90467dc983d54befe7a75ec2e09cc147b0caf96f2311720e166324153fdf24d`.
- Estimates.lean: `9926b173940a45c43c50684311a7de2af938917338f96a9c60b88a75e0d75bd3`.
- Frozen exponent contract: `7f3dcbd0c6e99538300bbfe307c2516440647ebd3999e28285439024c8b3a848`.

This is a source and proof-fidelity review. After I completed the source comparison, the root reported that the full exponent verifier passed all fifteen frozen statements and five definitions, including the reviewed Estimates implementation, at the default compiler limits. The root also reported unchanged parent-implementation, source, and frozen-review hashes and dependencies confined to trusted foundations. That is the root's completed verification result; I did not independently rerun the verifier. The separate implementation of Mean is outside this independent review's scope.

## Tail.lean: X.06–X.08 and X.13

**X.06, lines 10–26.** `column_square_sum_pos` has exactly the explicit population N, count vector, feasibility equality, and N≥2 arguments. The proof derives an actual positive count by contradiction: if every natural count is zero, their sum is zero, contradicting feasibility and N≥2. It then uses the positive normalized square as one summand of a nonnegative sum. No nonempty-alphabet, selected-digit, positive-square-sum, or uniform-positive-pile hypothesis is introduced. Zero unselected piles and a syntactically empty alphabet are handled by these same proved implications.

**X.07, lines 28–56.** `tailSquareFactor_eq_rpow_tailEdgeExponent` concerns the square-proportion tail product exactly. Positivity of N and its logarithm follows from N≥2; positivity of each square sum comes from X.06; positivity of the finite product follows locally. `Real.log_prod` computes its logarithm. Unfolding the source psi and tail exponent cancels the two minus signs, yielding the logarithm of this square product divided by log N. The positive-base real-power definition and `Real.exp_log` then prove the identity. No logarithm of the fixed-count collision product is used. M is arbitrary as frozen, including M≥K: the empty product is positive and the empty sum is zero without selecting a tail index.

**X.08, lines 58–64.** `tailCollisionFactor_le_rpow_tailEdgeExponent` composes the previously proved collision-factor comparison with X.07. It retains an inequality. It neither asserts equality nor requires a positive collision factor. In particular, a tail of singleton piles may have exact collision factor zero while the power remains positive.

**X.13, lines 66–75.** `tailEdgeExponent_at_full_length` omits both feasibility and N≥2 exactly as frozen. Each finite column index has value below K, so the filter requiring K≤its value is empty. The zero sum and total real division give zero for every N, including N=0 and N=1. This is an algebraic empty-tail conclusion, not a claim about interpreting a logarithm to base zero or one.

These are precisely the four permitted theorem declarations in Tail. Every auxiliary is a local proved fact; no new definition, instance, or named theorem appears.

## Estimates.lean: X.09–X.12 and X.14

**X.09, lines 9–54.** The signature retains exactly feasible counts, A≤M≤K, deterministic prefix extension, arbitrary real b, N≥2, and legality of x. Its local abbreviations L, epsilon, and E expand to the unchanged frozen definitions. The proof imports the established fourth-power mean bound, obtains the exact mean-power identity from X.05, and obtains the tail comparison from X.08.

The squaring step is justified by the existing nonnegativity of the collision factor; nonnegativity of its upper bound also follows by transitivity. This includes a zero collision factor and requires no hidden lower bound. Mean positivity is derived from the already proved legality lemma, rather than supplied as an assumption. The local power identities explicitly turn the natural fourth and second powers of positive-base real powers into exponents `4*(L+epsilon)` and `2*E`, using trusted real-power multiplication and natural-cast identities. Their product becomes the power of the sum through `Real.rpow_add`. Division by the positive constant four is preserved throughout. The final exponent and coefficient are exactly `4*(L+epsilon)+2*E` and `1/4`.

**X.10 and X.11, lines 56–95.** Both signatures add only the frozen real delta and the source condition `L<2*delta`. Each proof compares exponents using `linarith only [hsmall]` and monotonicity at base N≥1 derived from N≥2. Thus neither proof uses a sign for delta, L, E, b, or epsilon. The coarse result retains `2*E+8*delta+4*epsilon`; the singleton-shaped result retains `2*L+2*E+4*delta+4*epsilon`. Neither changes the branch premise to `L+epsilon<2*delta`, removes the signed correction, or assumes a singleton/stable-family predicate. The coefficient four on the error and the denominator four both match the frozen statements.

**X.12, lines 97–107.** The all-prefix ambient-size bound follows directly from the previously proved density-at-most-mean inequality and X.05. The conclusion is exactly the power with exponent `L+epsilon`; there is no small-mean premise or tail-positivity premise.

**X.14, lines 109–122.** The terminal theorem specializes X.12 at M=K with its displayed full-length legality and ambient length proof. The proof accepts the equivalent composed ambient length proof by proof irrelevance, adding no equality premise. It preserves the original ambient exponent and error. The separately proved X.13 supplies E=0 when describing the full terminal case; X.14 does not need to assume that identity or a small-size classification.

These are exactly the five permitted theorem declarations in Estimates. There are no additional definitions, instances, or named helpers.

## Boundary cases and source interpretation

Empty matrices, empty or equal-length prefixes, empty tails, selected pile count one, and deterministic tail columns are not discarded. The logarithmic theorems retain their explicit N≥2 domain; X.13 alone has the deliberately broader all-N empty-sum statement. The original population N remains in every inherited probability and numerical factor.

The proofs concern the existing absolute-coordinate density under the actual fixed-count product matrix law. They introduce no random recentering, reduced population, conditional exploration law, profile approximation, asymptotic error bound, or spatial concentration premise. They supply exact finite exponent consequences, including a singleton-shaped small-prefix bound and the terminal mean bound. They do not establish the stronger printed minus-cF spatial estimates or complete the outstanding stable-localization part of the original goal.
