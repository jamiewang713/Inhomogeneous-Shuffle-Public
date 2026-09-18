# Boundary encoding: independent adversarial review

Reviewer: `inequality_audit`. Decision: **approve all seven definitions and B1–B7 exactly as proposed**. This is a pre-implementation mathematical and interface review, not a claim that Lean code has already compiled.

Reviewed `MODEL_BRIDGE_CONTRACT.md` SHA-256:
`ff28431136dca4ea503c0c40a1350800e15f30ea188f54d6073f316bac516e20`.
The original `FROZEN_CONTRACT.md` remains at SHA-256
`5ba1c21dc9933186ebff72f9c502b286d15787db29d6d62961a9ea8bfe866f0b`.
No change to either contract or any Lean file was made in this review.

## Literal source comparison

The active boundary and admissibility definitions in
`time_inhomogeneous_riffle_shuffle_unified_article.tex:522–595` agree with
`stable_blocks/Riffle/Definitions.lean:84–129`: a boundary word either stops
at the first genuine crossing, including a crossing in column K, or has
length K and no crossing after the ambient prefix. The source one-based
range `M_w < j ≤ M_x` becomes the zero-based `Ico w.length x.length`.
The outward predicates in proposed definition 2 are exactly those used
by `Riffle.violations`, with strict inequalities in the opposite direction
to `Cross`.

`SparseAssignment` and `BoundaryCode` are used literally as defined in
`FirstMoment/Counting.lean:14–25`. In particular, sparse assignments store
values as well as positions, and the tag has a distinct sentinel `k`.

## Reconstruction and exact interfaces

Fix the existing `D`, `A`, and `s`. Put `m = A.w.length` and `n = x.length`.
The code contains the length, the guarded final crossing digit or sentinel,
and every outward index and its actual digit.

For each `i < n`, the specified decoder recovers `digit x i`:

1. If `i < m`, use the ambient prefix relation from boundary membership.
2. If `i` is outward, use the recorded value.
3. If `i = n-1` is the genuine crossing, use the tag. The crossing digit
   cannot simultaneously be outward, since the two strict inequalities
   are opposite.
4. Otherwise boundary membership gives no crossing at `i`, and absence
   from the sparse support gives no outward violation. Trichotomy then
   forces equality with `leftIndex A i` or `rightIndex A i`.

In the crossing branch all earlier new positions are noncrossing. In the
fallback branch `n = K` and every new position is noncrossing, including
the final position. This covers every position of the reconstructed word.

| Interface | Independent check |
| --- | --- |
| B1 `boundaryPositions_card` | The map from natural indices in the filtered `Ico m n` to `Fin K` is a bijection when `n ≤ K`. This proves equality of cardinalities. No legality is used; `n < m` simply makes both supports empty. |
| B2 `admissible_violations_le_budget` | If `v` is the natural number of violations and `r` is the source threshold, admissibility gives `(v : ℝ) ≤ r`, hence `v ≤ Nat.floor r`. Even a sign fact required by a floor API follows from this inequality and `0 ≤ v`; it is not an extra hypothesis. The existing setup also independently implies `r > 0`. |
| B3 `decode_encode_boundary` | The four reconstruction cases above prove literal equality with `x.val`. Legality supplies `n ≤ K` and bounds on all stored digits. |
| B4 `encodeBoundary_injective` | Apply the decoder to equal codes, then use B3 and subtype extensionality. |
| B5 `admissible_boundary_card_le` | B4 into the existing finite code type implies finiteness of the source. The target cardinality is `(K+1)*(k+1)*sparseCount K k budget`. No `Finite` or `Fintype` source premise is necessary. |
| B6 `encodePair_injective` | Apply B4 separately to the fixed left and right slots; pair and subtype extensionality finish. The source compatibility condition remains present, although it is not needed for injectivity. |
| B7 `admissible_pair_card_le` | B6 into the product of two finite code types gives source finiteness and the square of the B5 target cardinality. No extra source finiteness premise is necessary. |

The dependency order is acyclic: definitions 1–4, B1 and B2, definition 5,
definition 6, B3–B5, definition 7, then B6–B7. This is only an implementation
ordering observation; it changes none of the proposed interfaces.

## Adversarial cases

- **Crossing at K:** The proposed tag correctly keeps the last digit.
  A tag that instead used the sentinel for every length-K word would fail:
  take one uniform ternary column, `N=3`, empty ambient word, and
  `0 < chi < 1/3`. The admissible left-boundary words `[1]` and `[2]`
  both have empty outward support and the same length, so that alternative
  tag would identify them. The proposed definition distinguishes them.
- **Outward final fallback digit:** It must be included in the sparse
  support, as proposed. For one column with counts `(1,1,8)`, `N=10`,
  `chi=1/5`, `C=1`, and empty ambient word, the left index is 2. The legal
  fallback words `[0]` and `[1]` each have one violation, within the budget.
  Omitting the final support position, or omitting its value, would make
  them collide. The proposed definition keeps both position and value.
- **Full ambient prefix:** If `m=K`, boundary membership forces `x=w`.
  There are no new positions. The strict extension guard is false, the
  tag is the sentinel, and the ambient branch reconstructs the word.
- **K=0:** Legality forces `w=x=[]`; support and decoder output are empty.
  The strict extension guard prevents treating the totalized digit
  function at index zero as a genuine last digit.
- **Zero piles:** They create no gap. Stored values belong to the legal
  word, while the deterministic indices are legal by the already proved
  `Riffle.leftIndex_legal` and `Riffle.rightIndex_legal`. No all-piles-positive
  assumption is introduced.
- **Fixed parameters:** Injectivity is for a fixed `D`, `A`, and `s`,
  exactly as stated. The code does not identify the ambient word or the
  side. The ordered two slots in `encodePair` already fix the sides.
- **Arbitrary codes:** Some arbitrary codes may decode to illegal words;
  B3 only concerns codes produced by the encoder. Surjectivity and global
  legality of the decoder are neither needed nor asserted.

No retention, fluctuation, asymptotic, horizon, compatibility beyond the
existing pair subtype, or nonterminal condition is missing from B1–B7.
The proposed supplemental definitions and theorem interfaces need no
correction. Their implementation must preserve the stated support,
crossing guard, tag sentinel, decoder priority, and source subtypes.
