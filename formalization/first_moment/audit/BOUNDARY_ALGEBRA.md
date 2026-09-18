# Independent algebra review of the supplemental boundary contract

Decision: **APPROVE the exact proposed `MODEL_BRIDGE_CONTRACT.md`, definitions
1–7 and theorem interfaces B1–B7, without corrections or added assumptions.**

Reviewed proposed-document SHA-256:
`ff28431136dca4ea503c0c40a1350800e15f30ea188f54d6073f316bac516e20`.

This review compares the proposed interfaces with the authorized article's
boundary/admissibility definitions and the actual definitions and proved
lemmas in `Riffle.Definitions`, `Riffle.Model`, `Riffle.Boundary`, and
`Riffle.Retention`; prefix-word facts were checked in the imported
`Riffle.Words` module. No implementation or contract change was made.

## Exact definition review

1. `boundaryBudget` is the natural floor of the literal existing real
   admissibility threshold. `Nat.le_floor` converts the existing inequality
   directly; no additional nonnegative-threshold or integer-budget premise
   is necessary.
2. `outward` has the same strict inequality and side convention as
   `Riffle.violations`.
3. `boundaryPositions` uses absolute zero-based positions in
   `[A.w.length,x.length)`, transported into `Fin D.K`. This is exactly the
   source's one-based range `M_w < j <= M_x`. It includes the final position
   whenever that position is an outward violation.
4. The tag is selected by the guarded genuine-crossing condition, not by
   whether the word is terminal. Actual crossing digits lie below `D.k` by
   legality, while the distinct sentinel has value `D.k`.
5. The encoded length, tag, support, and actual support digits fit the existing
   `BoundaryCode` and `SparseAssignment` definitions without modification.
6. The decoder's specified priority order is correct. Ambient positions are
   restored from the fixed word; recorded exceptions override the default;
   a genuine final crossing is restored by the tag; every other position
   equals the relevant boundary index. Arbitrary codes need not decode to
   legal words, and the contract correctly makes no such assertion.
7. `encodePair` preserves the left/right order and uses the existing
   `AdmissiblePair` subtype, including compatibility. Proof irrelevance means
   no additional information is needed to recover its subtype element from
   the recovered pair of words.

## Exact theorem review

- **B1:** The sole premise `x.length <= D.K` suffices. Sending a recorded
  `Fin D.K` index to its natural value is a bijection onto the finite
  `Ico/filter` defining violations. No digit-range or legality fact enters
  this cardinality equality. If `x.length < A.w.length`, both sets are empty.
- **B2:** This is exactly `Nat.le_floor` applied to the second conjunct of
  admissibility. It neither changes the real threshold nor assumes an
  independent integer bound.
- **B3:** Boundary membership gives the complete crossing-or-fallback
  dichotomy. At a non-recorded, non-crossing position, the negations of both
  opposite strict inequalities force equality with the boundary index.
  Together with `digit_prefix`, this proves pointwise reconstruction.
  `List.ext_getElem` and the stored length give equality of words.
- **B4:** The left inverse in B3 proves injectivity, followed by `Subtype.ext`.
- **B5:** The code cardinality is exactly
  `(D.K+1)*(D.k+1)*sparseCount D.K D.k (boundaryBudget A)`. The injection
  proves finiteness of the source subtype, so no finiteness premise is needed.
  The statement using `Nat.card` has the stipulated conclusion.
- **B6:** Apply B4 independently to both code components, then product and
  subtype extensionality. Compatibility is retained in the source; it does
  not need an independent encoded field.
- **B7:** The target is the product of two identical finite code types.
  Its cardinality is exactly the square displayed in the contract. Finiteness
  again follows from the injection without an assumed finite instance.

## Boundary cases and dependency checks

- A genuine crossing at column `D.K-1` has length `D.K` and keeps its actual
  digit. A no-crossing fallback of the same length instead gets the sentinel.
- An outward final digit in a no-crossing fallback is recorded in the support;
  dropping it would break reconstruction, and the contract does not drop it.
- If the ambient prefix is terminal, legality and prefix length force every
  admissible boundary word to equal the ambient word. The support is empty
  and the tag is the sentinel. This includes `D.K=0`.
- An empty ambient prefix permits a genuine crossing in the first column;
  the guard and zero-based last index handle it correctly.
- Zero piles require no positivity assumption beyond existing word legality.
  `leftIndex_legal` and `rightIndex_legal` already show the deterministic
  default digits are legal. Unused or impossible code combinations merely
  overcount the actual image.
- A budget larger than `D.K` is harmless: the frozen `sparseCount` and its
  cardinality theorem already include vanishing binomial terms beyond `D.K`.

Existing project facts sufficient for reconstruction include
`admissible_mem_boundary`, `boundary_mem_desc`, `digit_prefix`,
`leftIndex_legal`, `rightIndex_legal`, and the literal `BoundaryCut`
dichotomy. `boundary_nonterminal` alone must not be used to dismiss the
genuine-crossing branch at length `D.K`. No retention or fluctuation theorem
is required by these interfaces.

The required support transport, default-digit equality, and reconstruction
steps are proof-local deterministic consequences, not missing hypotheses.
The contract correctly avoids claiming that all stable words inject into
`ProfileKey`: different regular-digit arrangements may belong to one profile
class and are handled by entropy counting instead.

The original 29 frozen interfaces remain untouched by this approval.
