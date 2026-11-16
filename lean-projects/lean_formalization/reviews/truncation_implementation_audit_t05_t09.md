# Independent implementation audit: T05 and T09

**Both implementations are mathematically approved against the unchanged
frozen truncation contract.** No changed assumption, endpoint condition,
stopping convention, or cardinality target was found. This audit examines
the definitions and proof arguments; kernel builds remain separate.

Audited SHA-256 digests:

- `RiffleProfiles/BoundaryCounting.lean`:
  `c6eedca5ba8c37701aa3d7318f567c10956f8b79cd5972bf9a87fe3dabf3c4dc`.
- `RiffleProfiles/MatrixTruncation.lean`:
  `7818feb0eb34875409d331edbbe21a187c4edd22f89d6cb062f3f0e3c5100a92`.
- Examined dependency `RiffleProfiles/MatrixLaw.lean`:
  `0a054b43828a0c9c7d0a6051525c9957be2abac39e8691ec33aa6d95f443da60`.
- `FROZEN_TRUNCATION_CONTRACT.md`:
  `d1cd3287aa31cb0b3236c9cf811399a63a648b435d299cfaa0dbd789e2406a66`.

## T05: actual boundary descriptors

`boundarySparseSupport` (lines 47–53) is exactly the frozen relative set:
it records `t : Fin D.K` with `t.val+1 < |x|-|w|` and an actual violation
at the absolute index `|w|+t.val`. It does not substitute absolute indices
for relative ones or include the separately stored final digit.

`boundarySparseSupport_card_le` maps that set to the actual violation
set by `t ↦ |w|+t.val`. Its shift is injective by natural addition
cancellation, and the defining strict bound puts its image inside
`[|w|,|x|)`. The proof therefore bounds the cardinality of the exact sparse
support by `Riffle.violations`; `admissible_violations_le_floor` then uses
the unchanged weak admissibility test to obtain `violations ≤ floor(tau)`.
This is the correct low-count threshold, distinct from T03's strict
discard threshold `floor(tau)+1`.

The pattern labels are the actual digits at their shifted positions
(lines 95–106). Legality proves those labels lie in `Fin D.k`.
`boundaryFinalDigit` (87–93) stores the actual last digit whenever the
extension is nonempty, without testing whether it crosses the boundary.
Thus a violating final digit in terminal fallback is preserved. Only an
empty extension uses zero; `D.two_le_k` provides that digit. The descriptor
stores `|x|-|w|` in `Fin (D.K+1)` and proves both frozen descriptor
constraints, including the zero default.

Reconstruction is substantive, not a postulated decoding property.
`boundary_no_earlier_cross` handles both alternatives in the source
`BoundaryCut`. `boundary_forced_extreme` combines absence of crossing and
absence of violation to recover every unrecorded pre-final digit.
`descriptor_prefinal_digit` uses this fact outside the sparse support and
the stored actual label inside it.

`admissibleBoundaryDescriptor_injective` (153–191) first recovers absolute
length from relative length using the proved ambient-prefix length bounds.
It then recovers each list digit in three exhaustive cases: inside the
fixed ambient prefix, the separately stored final position, or a relative
pre-final position. Equality of descriptors gives equality of the stored
data; it does not assume the words agree beyond a prefix. Finally list
extensionality gives equality of the admissible-word subtypes.

This covers empty extensions and `K=0`: every existing list digit then
belongs to the fixed ambient prefix. A nonempty extension's final index
is proved in range before any digit lookup. Zero piles introduce no new
premise; the existing legal-boundary subtype already excludes an
impossible selected digit.

The `admissibleBoundaryFinite` instance is **derived from that injection**
(193–196), so the subsequent `Nat.card` bound is not exploiting the value
zero assigned to an infinite type. The target is the actual subtype of
natural-number lists satisfying `Admissible`, and the bound is precisely
`B = k*(K+1)*lowCount K (floor(tau)) k`. No unrestricted list or full-index
suffix is counted. The pair component map is injective, yields derived
finiteness of the actual `AdmissiblePair` subtype, and bounds its `Nat.card`
by the product of the two boundary counts, hence `B²`. Compatibility is
retained in the domain and can only reduce that count.

## T09: expected truncation counts under the matrix law

The first two theorems in `MatrixTruncation.lean` (14–33) use the existing
dependent product `Shuffle.fixedMatrixLaw (modelHistogram D)` and count
rows in the exact discarded-boundary events. The one-side event is the
frozen `discardedBoundary`; the two-side event is its union, so a row in
both events is still counted once. Rewriting by the proved
`model_expected_row_count` and applying T04 preserves the exact `N` and
`2` factors. No new theorem premise is introduced.

The private event-transport lemma (35–51) is the reviewed finite image
construction. For an arbitrary predicate `E` on complete indices it sets
`EL = fullList '' {omega | E omega}`. Its proof of
`fullList omega ∈ EL ↔ E omega` uses the existing injectivity of
`fullList`, not an assumed inverse or a prefix-invariance condition.
It then applies T08 and T01 to identify the exact expected row count with
`N * Σomega indicator(E omega)*wordWeight omega`.

`model_exceptionalPrefix_expected_rows_le` (53–68) retains precisely
`P.IsRegular chi C`, positive `chi`, and nonnegative `alpha` as additional
data beyond `Model`; `N≥2` is derived from `D.one_lt_N`. The endpoint
functions remain arbitrary functions of the full index. The row predicate
uses the literal source exceptional filter and the strict normalized
cardinality test. Its conclusion is exactly
`N * tailWeight K (floor(alpha*logScale N)+1) (k*(3*chi))`.
The final proof substitutes the unchanged coordinate identity
`modelColumnProfile_prob` into the scaled T06 result. It introduces no
legality, full-support, deterministic-endpoint, or endpoint-order premise.

The examined T08 dependency samples **unsorted labelled rows**. Its word
marginal follows from uniform-column symmetry and the existing column
product rectangle theorem, while its expected-cardinality identity uses
finite linearity of expectation. Neither proof assumes independent rows.
The added dependent `Fintype` instance in `MatrixLaw` enumerates the same
finite matrix type and introduces no probability-law hypothesis. A
particular sorted row's marginal is not used anywhere in T09.

## Scope

The files establish frozen finite T05/T09 conclusions. They do not prove
the previously false coarse-profile fibre estimate, an ordered-limit
bound, or a sorted shuffle-graph edge estimate. No Lean code, source
definition, or frozen statement was edited during this audit.
