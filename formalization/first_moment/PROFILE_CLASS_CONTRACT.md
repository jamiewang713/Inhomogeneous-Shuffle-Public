# Actual profile-class counting: supplemental contract

Status: FROZEN at 2026-09-17T21:21:36.340505+00:00, following three independent approvals. No Lean implementation existed at freeze.

This supplements the original 29-theorem contract and the seven boundary-model bridges without changing either freeze. It constructs the actual refined descriptors of admissible stable-word triples and counts their realized classes. It does not assert injectivity of individual words or a within-class entropy bound. The mathematical sources remain the three user-authorized files; definitions are compared with TeX `def:space-time-digit-profile` and the first-moment proof's explicit inclusion of exceptional digit values.

The namespace is `InhomogeneousShuffle.FirstMoment.Model`; the implementation will be `FirstMomentModel/ProfileClasses.lean`. All model data are the existing `D : Riffle.Model` and `A : Riffle.Setup D`. Additional universally quantified deterministic data are a natural cell count `c`, `cell : Fin D.K -> Fin c`, `good : Fin D.K -> Nat -> Prop`, and a real exceptional cutoff `alpha`. A routing function into `Fin 4` is specified after the actual stable-word domain is defined. These functions are data, not hypotheses of regularity, probability, or convergence.

## Exhaustive definitions

1. `exceptionalPositions A good y z x : Finset (Fin D.K)` is the finite set of all `i` for which `(Riffle.join y z).length <= i.val < x.length` and `not (good i (Riffle.digit x i.val))`. Both endpoints follow the source's zero-based extension convention; no ambient-prefix positions are included merely because they follow `A.w`.
2. `goodDigitCount A cell good y z x a l : Nat`, for `a : Fin c` and `l : Fin D.k`, is the cardinality of the finite set of all `i : Fin D.K` in that same extension range satisfying `cell i = a`, `Riffle.digit x i.val = l.val`, and `good i (Riffle.digit x i.val)`. These are natural counts, before division by `log N`.
3. `exceptionalBudget A alpha : Nat` is `Nat.floor (alpha * Real.log (D.N : Real))`.
4. `ProfileWord A good alpha` is the subtype of triples `p : Riffle.Word × Riffle.Word × Riffle.Word`, ordered as `(y,z,x) = (p.1,p.2.1,p.2.2)`, with the conjunction:
   - `Riffle.AdmissiblePair A y z`;
   - `x in Riffle.Stable A y z`;
   - `((exceptionalPositions A good y z x).card : Real) <= alpha * Real.log (D.N : Real)`.

   The real cutoff remains in this definition. It is not replaced by a floor inequality; in particular a negative `alpha` does not acquire spurious zero-exception words. No additional legality, retention, nonterminal, or finiteness field is added.
5. For any `route : ProfileWord A good alpha -> Fin 4`, `encodeProfile A cell good alpha route` maps each element `p` of that subtype to the existing

   `ProfileKey D.K D.k (boundaryBudget A) (exceptionalBudget A alpha) (c*D.k)`.

   Its fields, in the existing key order, are the proved left and right `encodeBoundary` values; `x.length` as `Fin (D.K+1)`; the natural good-digit counts as a vector `Fin (c*D.k) -> Fin (D.K+1)` using the inverse of the standard `finProdFinEquiv : Fin c × Fin D.k ≃ Fin (c*D.k)`; the sparse assignment of exactly `exceptionalPositions` with each actual exceptional digit value; and `route p`. Length and digit bounds follow from the proved stable-word legality, and the exceptional cardinality bound follows from the real cutoff. No independent integer-budget hypothesis is assumed.
6. `ProfileClass A cell good alpha route` is the subtype of this same finite `ProfileKey` consisting exactly of `Set.range (encodeProfile A cell good alpha route)`. Thus classes are realized descriptors, equivalently equality fibers of the encoder. Distinct stable words can belong to the same class.

## Exhaustive theorem interfaces

P1. `profileWord_exceptional_budget`: for every `p : ProfileWord A good alpha`, the exceptional support cardinality is at most `exceptionalBudget A alpha`. The only assumptions are those already present in the subtype; `alpha >= 0` is not added.

P2. `goodDigitCount_le`: for every `y,z,x : Riffle.Word`, `a : Fin c`, and `l : Fin D.k`, `goodDigitCount A cell good y z x a l <= D.K`. There is no legality, length, or source-finiteness hypothesis.

P3. `encodeProfile_eq_data`: for any `p,q : ProfileWord A good alpha`, equality of their `encodeProfile A cell good alpha route` values implies the conjunction of all seven facts below:

   - their left boundary words are equal;
   - their right boundary words are equal;
   - their stable-word lengths are equal;
   - for every `a : Fin c` and `l : Fin D.k`, their natural `goodDigitCount` values are equal;
   - their `exceptionalPositions` finsets are equal;
   - for every `i : Fin D.K` in the exceptional support of `p`, the actual stable-word digits of `p` and `q` at `i.val` are equal;
   - `route p = route q`.

   There is no conclusion asserting equality of the stable words or equality of their exact `cL` exponents. The statement uses the actual labeled exceptional support, without weakening equality to cardinality equality.

P4. `profileClass_card_le`: without a `Finite` or `Fintype` hypothesis on the stable-word domain or class type,

`Nat.card (ProfileClass A cell good alpha route) <= profileCountBound D.K D.k (boundaryBudget A) (exceptionalBudget A alpha) (c*D.k)`.

The bound is precisely the existing frozen count, hence equals

`4*(D.k+1)^2*(D.K+1)^(c*D.k+3)*sparseCount D.K D.k (boundaryBudget A)^2*sparseCount D.K D.k (exceptionalBudget A alpha)`.

No other definitions or exported theorems are planned. Proof-local intermediate facts may be used without changing these interfaces.

## Source specialization and limits

For the source, `c` is the number of time cells times the number of simplex-partition cells. `cell` encodes both indices. `good i a` means that `a` is a valid digit and its representative probability exceeds `2*chi`. Set `alpha` to the source exceptional cutoff. Because `D.N > 1`, the real cutoff in `ProfileWord` is equivalent to the source normalized bound on `R_x`; natural good counts similarly determine the normalized profile counts.

Admissible pairs are retained by the existing proved theorem; this is not an extra domain assumption. Terminal and nonterminal fallback words stay in the domain until the source numerical margin excludes the latter. When `x = join y z`, the extension, good counts, and exceptional support are empty. `K=0`, empty cells, negative `alpha`, and budgets larger than `K` require no extra hypotheses. Arbitrary codes need not be realized.

The arbitrary routing function makes at most four categories and must later be instantiated with the density-case routing. This theorem does not assert that any proposed routing satisfies those density bounds. For the source representatives, the stored data fix the profile entropy and the other count-defined quantities; they do not make the exact block-size exponent constant. The eventual `N^epsilon` bound still requires the existing parameter choices and a fixed number of cells before `N` tends to infinity.

## Review and verification

The independent algebra, statement, and adversarial reviews must approve this exact document before implementation and a hash must be recorded at freeze. They have already agreed on the real-budget domain, exact extension range, exceptional-value refinement, zero-parameter cases, arbitrary deterministic cell/good/route data, and the distinction between a class count and a word-fiber count. All four results must compile and pass the standard-foundation dependency audit; both earlier contracts remain immutable.
