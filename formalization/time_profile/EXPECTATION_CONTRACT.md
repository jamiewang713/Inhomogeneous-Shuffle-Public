# Expected cylinder and side-mass interface

Status: FROZEN after independent mathematical, Lean-design and adversarial review of every definition and every P01–P08 statement, 2026-09-17. All three reports explicitly approve this exact inventory, including normalized-legality domains and the noncircular P02/P03 dependency order, before any implementation. The original and analytic frozen contracts remain unchanged. This file's checksum is recorded separately.

This closes the expectation/product-mass obligation expressly left in the original frozen contract. It changes no existing definition or scientific assumption. The source law is the uniform law on all labelled matrices with the prescribed column counts, as in 2510 Section 2.2 and the unified article's shuffle-matrix model. Columns are independent because this finite sample space is a Cartesian product with uniform law; row independence is neither assumed nor asserted.

## Definitions to freeze

For cuts: Cuts k N K, define ColumnAssignments(cuts,j) as the finite type of functions a:Fin N -> Fin k having exactly cuts.count j l occurrences of each l. Construct its nonemptiness from cuts.sum_count, rather than making it a field or hypothesis. One permitted construction chooses an equivalence Fin N ~= (Sigma l:Fin k, Fin(cuts.count j l)) and projects to the digit coordinate.

The labelled sample space is Omega(cuts)=Pi j:Fin K, ColumnAssignments(cuts,j), with discrete measurable space and the actual probability measure obtained from PMF.uniformOfFintype Omega. A sample's entry at labelled row i and column j is its j-th assignment applied to i. This is a uniform fixed-count matrix, without an auxiliary canonical-array premise or a changed sampling law.

For a finite family of allowed digit sets A_j, boxRows(A,sample) is the set of labelled rows whose j-th entry belongs to A_j for every column. prefixRows(x,M,sample) is the set matching x at every j.val<M; all later entries are unrestricted. M<=K in source applications.

For j:Fin K, leftSideRows(x,j,sample) matches x in every column h.val<j.val and has entry at j strictly less than x_j. rightSideRows uses strictly greater. Every later column is unrestricted. For w<=j.val these are exactly the source side pieces inside ambient prefix x before w, with extension fixed until the column before j. Their expected cardinalities are unconditional expectations of global labelled-row counts restricted to the ambient event; they are not conditional-on-ambient-size expectations.

Expected side maxima use the same existing positions(w,v), nonnegative-real supremum with empty maximum zero, square roots and extended logExponent as the frozen cF. Thus the expectation-based fluctuation exponent is the logarithm of square roots of maxima of EXPECTED side counts. It is not the expectation of a random fluctuation exponent or of a random maximum.

## Theorem inventory for comparison

### P01 — Source law exists and conserves column counts [F/P]

For every natural k,N,K and every Cuts k N K, each ColumnAssignments type and Omega are finite and nonempty. Every sample has exactly the prescribed column counts; consequently every digit that occurs in a labelled row has positive prescribed count. For N>0, using the existing normalized profile, observed row prefixes satisfy the existing LegalPrefix predicate. The uniform sample law is a probability measure. Its finite-integral formula is the ordinary arithmetic average over all samples. No unproved finite/cardinality/integrability premise is introduced.

### P02 — Labelled-row symmetry and marginal law [F/P]

Row reindexing by any permutation is an equivalence of a column-assignment type, preserving the prescribed counts. Uniform averages are invariant under this equivalence. For N>0, every fixed UNSORTED labelled row i, column j and real function g on Fin k,

E[g(entry(i,j))] = sum_l ((cuts.count j l)/N) g(l).

The same marginal holds under the uniform full matrix law. In particular a single digit event has probability count/N. No claim is made about the marginal of a row after sorting. There is no independence assertion between distinct rows.

For implementation order, the column component of P02 uses P01 and row symmetry; its full-matrix component may use P03. P03 depends only on P01 and finite product-of-sums, so there is no circular dependency.

### P03 — Column product factorization [F/P]

For arbitrary real functions F_j on the j-th column-assignment type,

E[product_j F_j(column_j)] = product_j E_uniformColumn[F_j].

This is proved from the finite Cartesian-product uniform law, including K=0. Any generic finite-uniform helper must derive its normalization and integrability, not add an independence field. Correct one-column marginals alone are not sufficient to invoke this theorem.

### P04 — Expected box occupancy [F/P]

For N>0 and any allowed finite digit sets A_j,

E[card(boxRows(A))] = N * product_j (sum_{l in A_j} prob(p_j,l)),

where p_j is the existing cuts.profile. The proof sums labelled-row indicators and uses P02/P03. It does not assume independent rows. Empty allowed sets, zero piles, empty column families and empty intersections are covered by the exact finite formula.

### P05 — Ambient cylinder identity [F/P/A]

For N>0, any digit array x and M<=K,

E[card(prefixRows(x,M))] = prefixMass N p x M.

There is no legality requirement for this mass identity: impossible cylinders have mass zero on both sides. For N>=2 and the exact legality/ordered-prefix hypotheses of existing D04, substitute this identity into D04 to identify the logarithm of the expected cylinder size with the existing cL and the actual ambient birth-exponent discrepancy. No positivity or b>=0 assumption is added.

### P06 — Side-piece identities [F/P]

For N>0, x, j:Fin K and w<=j.val,

E[card(leftSideRows(x,j))] = sideMass N p x w leftProbability j,

E[card(rightSideRows(x,j))] = sideMass N p x w rightProbability j.

There is no legality requirement or positive-side hypothesis; empty side pieces have zero expectation. The ambient prefix and extension factors are split at the exact w, using the existing finite product identity. Later digits are not constrained.

### P07 — Expected-size interpretation of cF [F/P/A]

For N>=2 and w<=v<=K, each expectation-based side maximum equals the corresponding existing sideMaximum, and the expectation-based fluctuation exponent equals the existing cF in WithBot Real. This includes v=w and bottom-valued cases. It is an identity of deterministic quantities built from expected cardinalities and makes no anti-concentration assertion.

### P08 — Sorting preserves the counted cardinalities [F/P]

For every matrix, any permutation of its rows and any predicate on complete row words, reindexing rows preserves the number satisfying the predicate. The permutation may depend arbitrarily on the sample, so no independence from the matrix is needed. Consequently the P05/P06 expected-cardinality formulas are unchanged after any such reindexing, in particular a permutation used for lexicographic sorting. This statement concerns cardinality only; no shuffle-graph or endpoint-localization theorem is inferred.

## Fidelity constraints

The existing prefixMass, sideMass, cL, cF and all time/digit-profile definitions remain unchanged. The sample law and all finite expectation formulas must be concrete, not fields postulating the desired result. All statements are exact finite formulas with explicit N domains and prefix domains. There are no limiting assertions or additional time-profile hypotheses in this interface. The false source cF anti-concentration consequence remains outside these identities.
