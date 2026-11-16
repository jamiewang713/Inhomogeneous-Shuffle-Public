# Independent post-implementation boundary review

Decision: **PASS.** The implementation matches the frozen supplemental
contract exactly, with no altered theorem hypotheses or conclusions and no
additional exported definitions or theorems.

Reviewed files and SHA-256 values:

- `FirstMomentModel/BoundaryEncoding.lean`:
  `e880ccb74ee71c0cd0644bb39f5bcdb709cef02c46d43c8ef30b1d73fdc0b31f`
- `MODEL_BRIDGE_CONTRACT.md`:
  `7d04c06ab51c086bf97d60e3b52caac9b798cdb07b7b0cb5b99ea7a78042cbc5`

This was a read-only comparison of code and contract. Compilation and the
dependency audit are being checked separately by the root agent. No code,
contract, or previously pinned review file was modified.

## Definition comparison

The file exports exactly the seven frozen definitions in namespace
`InhomogeneousShuffle.FirstMoment.Model`:

1. `boundaryBudget` is the exact natural floor of the source threshold.
2. `outward` uses the stipulated strict inequality on each side.
3. `boundaryPositions` includes exactly absolute indices in
   `[A.w.length,x.length)` satisfying `outward`, including a final fallback
   violation.
4. `boundaryTag` uses the conjunction of strict extension beyond the ambient
   word and `Cross` at the last digit. Its genuine-crossing branch stores the
   legal digit; its other branch is `Fin.last D.k`. It does not incorrectly
   identify every length-K word with fallback.
5. `encodeBoundary` stores the actual length, the frozen tag, the exact support,
   and the actual digit values. The support-budget proof uses B1 and B2.
6. `decodeBoundary` uses the exact frozen priority: ambient digit, sparse
   recorded digit, final tag if below k, then side default. Its `i+1=length`
   test is equivalent to the stipulated final-position condition for the
   index being decoded. It returns a word for every code without asserting
   legality of arbitrary decoded words.
7. `encodePair` preserves the left/right order and the full source
   `AdmissiblePair` subtype, including compatibility.

No original counting or stable-block definition is redefined.

## Theorem comparison

The file exports exactly B1–B7 under their frozen names:

- `boundaryPositions_card` has only `x.length <= D.K` as its word hypothesis;
  the proof is the promised finite-index bijection.
- `admissible_violations_le_budget` has only admissibility as its word
  hypothesis and proves the exact integer bound using `Nat.le_floor hx.2`.
- `decode_encode_boundary` has no additional premise beyond its admissible
  subtype. The proof treats both boundary-definition branches, including a
  genuine crossing at the final column.
- `encodeBoundary_injective` follows from reconstruction and subtype
  extensionality with no added assumption.
- `admissible_boundary_card_le` has the exact coefficient
  `(K+1)*(k+1)*sparseCount K k budget`, and has no source `Finite` or `Fintype`
  premise. Its finite instance is local and belongs only to the code type.
- `encodePair_injective` applies the two boundary injections and restores the
  word pair by extensionality.
- `admissible_pair_card_le` has the exact squared cardinality bound and no
  source finiteness premise.

The declaration inventory contains seven definitions and seven theorems;
all other implementation facts and finite instances are proof-local. There
are no extra retained/nonterminal/fluctuation/good-column assumptions.

## Edge cases checked against the proof

- Final-column crossings are handled by `hcross`, without excluding length K.
- Fallback reconstruction uses no-crossing at every suffix position and the
  sentinel tag. An outward last digit has already been restored by the sparse
  branch.
- Terminal ambient words and K=0 create no invalid last-index obligation:
  the crossing-tag guard requires positive extension; decoding uses only
  indices below the stored length.
- Empty ambient prefixes allow first-column crossings normally.
- Digit bounds come from existing legality, so zero piles cause no added
  positivity requirement. No arbitrary-code legality claim is made.

No mismatch or additional mathematical assumption was found.
