# Frozen implementation record: concrete realization of X1

Status: FROZEN before realization code, after the root compared the independent probability, Lean-representation, and missing-hypothesis reviews. This instantiates the two experiments already specified by X1 and the positive-conditioning convention already specified by F3. It does not repair or alter an ambient theorem or change frozen contract v1. No additional reserve premise is allowed.

## Definitions to instantiate

- `L : ℕ` is the side-pile size. The exported X1 conclusions retain `1 ≤ L`.
- The Boolean `singleton` selects exactly the two frozen cases: `false` means balanced middle size `L`, and `true` means singleton middle size `1`.
- The labelled population is `Fin (2*L + middleSize)`.
- Its three-digit histogram is `(L, middleSize, L)`, with feasibility proved by summing the three entries.
- For `d : ℕ`, use `Fin (d+2)` columns, each with that histogram. The sample space and law are the existing D6 `FixedColumn` product and `fixedMatrixLaw`.
- The first-column middle-row reveal is the function sending a matrix to its finite set of rows with first digit `1`. Additional revealed information can be included in an arbitrary finite reveal or positive event; the deterministic endpoint identities hold regardless of it.
- The first-prefix left endpoint is the number of labels with first digit `< 1`; the right endpoint is the number with first digit `≤ 1`. These are literal first-digit lexicographic counts, not new asymptotic or stable-prefix definitions.
- These quantities will be named `leftCount` and `throughCount`: they are zero-based cumulative endpoint counts. A one-based position convention adds the same fixed `1` to both. The exact residual hypergeometric variable is the count, so no indexing convention is silently identified with a different random variable.
- The residual population is the set of first-column labels with digit different from `1`; the marked residual labels are those with digit `0`. The sample is the entire residual population, exactly as in the source's first-column equal-index case.

## Theorem conclusions to implement

R1. For every legal matrix in either frozen experiment, the first-column middle, residual, and marked counts are respectively `middleSize`, `2*L`, and `L`; the endpoints are `L` and `L+middleSize`.

The marked set is contained in the residual population, the sample set is exactly that population, and `(markedRows ∩ sampleRows).card = leftCount`. Thus the residual variable is visibly the actual finite intersection count, not an unrelated variable with a matching numerical law.

R2. Under the explicit product law, for every positive conditioning event `E`, the conditional law of the left endpoint is exactly `exhaustedParams L` at every natural value. Thus the conditional expectation is `L`, conditional variance is zero, and the conditional atom at `L` has probability one. The right endpoint has a unit conditional atom at `L+middleSize`. Positivity is the existing F3 normalization requirement, not an added ambient reserve assumption.

R3. For any retained event `S` and positive `E`, the conditional probabilities of `(left=L) ∧ S` and `(right=L+middleSize) ∧ S` both equal `P(S | E)`. This prevents selecting a high-probability retained event from creating endpoint randomness. It makes no incorrect claim that an unconditionally likely `S` is likely on every conditioning atom.

The finite-tower consequence, using frozen F4, is also part of R3: for any finite reveal `Z` and real `b`, if the sum of those two restricted point probabilities is at most `b` on every positive reveal atom, then `2*P(S) ≤ b`. This is a consequence of a proposed point-probability bound, not an assumption inserted into a shuffle theorem. No lower bound on each individual `P(S | Z=z)` is used.

R4. For every positive atom of the actual middle-row reveal, the same conditional law conclusions hold. The actual residual sample complement equals zero for `L≥1`; all marked and unmarked residual sizes are positive. No fibre of probability zero is assigned a conditional probability law.

## Explicit boundary

This formalizes the finite D6 matrix realization and the source's first-column equal-index reveal obstruction. It does not invent precise meanings for the manuscript's `o(1)`, `O(δ)`, unspecified uniformity constants, or arbitrary exploration sigma-field. Crossing, admissibility, and fluctuation-regularity in the manuscript remain subject to the independent source audit unless their exact already-frozen finite definitions can be translated without a new target or changed hypothesis. No statement of complete formalization of the ambient/stable-prefix theorem will be made.
