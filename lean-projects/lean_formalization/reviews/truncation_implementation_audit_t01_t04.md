# Independent implementation audit: T01–T04

**Approved mathematically against the unchanged frozen T contract.** No
additional hypothesis, changed event, or altered threshold was found.
This is a read-only proof and statement audit; the implementing agent is
responsible for the separate kernel build and elaboration repairs.

Audited SHA-256 digests:

- `ModelWordMass.lean`:
  `e8c01f12b085b3d878b8199b42a8ee3fde5e951a5a253976af83b8cda8852e7d`.
- `BoundaryTruncation.lean`:
  `d3f58a42930c6afcbe523bef628522a3df8bd5b5949dd05ca1f27d4ff8805cd6`.
- `FROZEN_TRUNCATION_CONTRACT.md`:
  `d1cd3287aa31cb0b3236c9cf811399a63a648b435d299cfaa0dbd789e2406a66`.

## T01 and T02

`modelDigitProb` is exactly the real coercion of the existing `Riffle.prob`
at the specified finite indices (`ModelWordMass.lean:14–15`). The
nonnegativity and column-sum proofs use the existing nonnegative counts
and normalization, with the correct conversion from `range D.k` to
`Fin D.k`. `modelColumnProfile` stores those coordinates in the existing
simplex, and its coordinate identity is reflexive.

The weight identity and `model_expectedCount_eq_wordMass` (lines 34–50)
coerce the literal source product functional. The latter retains the
factor `D.N`, the original set `E`, and precisely the event
`fullList ω ∈ E`. It does not restrict to positive-weight words or assume
a stochastic identification. Illegal alphabet-bounded words have zero
product weight; empty column indices give the usual empty product.

`model_expectedCount_le_tailWeight` (lines 52–77) has exactly frozen T02's
bad-digit family, threshold, nonnegative tail parameter, coordinate
bad-mass bound, and event-inclusion premise. Its pointwise comparison is
valid when either event fails because all product weights are
nonnegative. The final application is the proved F18 union-tail theorem;
`Fintype.card_fin` gives exactly `D.K`. No coordinate or row independence
premise is introduced.

`model_expectedCount_union_le` (lines 79–89) is the reviewed finite union
subadditivity helper. It keeps the common `N` factor and proves the
indicator inequality in all four membership cases. Overlap requires only
nonnegative mass, not disjointness.

## T03

`boundaryThreshold`, `boundaryBadDigits`, and `discardedBoundary` are
exactly the frozen definitions (`BoundaryTruncation.lean:11–23`). In
particular, the discarded event requires an ambient full legal word and
failure of the **actual selected prefix's** admissibility test. It is not
a test on an arbitrary prefix or a different stopping rule.

`boundaryThreshold_pos` uses only `Setup` and `Model`: `chi<1/k≤1`,
positive `chi`, positive `C`, and `N>1` give positive denominator and
numerator logarithms. `boundaryBadDigits_small` applies the existing
strict small-pile theorems with the valid finite index bounds, including
zero-count piles.

`boundary_violations_le_badCount` (lines 45–73) preserves the exact source
violation range `[|w|,|x|)`. Its sole extra local premise is the reviewed
prefix relation `x <+: fullList ω`. This implies `|x|≤K`; membership in
the violation set gives `i<|x|`. The source prefix-digit and full-list
identities then identify each violation with a bad full-word position.
The proof includes the natural violation set in the image under
`Fin.val`, and uses the injectivity of `Fin.val` to obtain equality of
image and source cardinalities. Thus no multiplicity or suffix is lost.
This argument does not need `x` to extend `w` or have positive weight;
its stated prefix premise is sufficient even when the violation range
is empty.

`discardedBoundary_many_badDigits` (lines 75–87) first obtains boundary
membership and the prefix relation from `selected_spec`. This makes
failure of `Admissible` equivalent to the strict inequality
`boundaryThreshold < violations`. The natural-floor equivalence is used
with a proved nonnegative threshold, followed by `add_one_le_iff`.
Consequently the threshold is exactly `floor(tau)+1`, including integral
values of `tau`. It does not become `ceil(tau)` or `floor(tau)`.

No genuine-crossing or nonterminal premise is introduced. Terminal
fallback uses the same selected-prefix specification. When the ambient
word already has length `K`, selection has an empty extension and zero
violations, so the discarded event cannot occur. This includes `K=0`.

## T04

`discardedBoundary_expectedCount_le` (lines 89–100) applies T02 with the
actual event and threshold proved under T03. The strict per-digit bound
is weakened only inside the proof to the weak bound required by F18;
`badDigitMass_le` gives the exact coordinate parameter `D.k*chi`.
There are no new theorem premises or missing cardinality factors.

`discardedBoundary_union_expectedCount_le` (lines 102–113) combines
finite union subadditivity and the two identical one-side bounds. Its
right side is exactly `2*(N*tailWeight K (floor(tau)+1) (k*chi))`.
Terminal status is neither used as an extra exclusion condition nor as
an exemption from admissibility.

These files establish finite product-functional bounds only. An actual
matrix expectation requires frozen T08/T09, and sorted-edge and
asymptotic conclusions remain separate obligations. No Lean code or
frozen contract was edited during this audit.
