# Independent adversarial review of P01–P05

Reviewed candidate: `PROFILE_SOURCE_CANDIDATE.md`, SHA-256
`c68c9f8a5b34671e45813e297ea009a17c59187cc41faf891fd8fbfd47c34e7b`.
This is a preimplementation review. All five proposed statements and the three
specified Analysis proof-compatibility repairs are approved. No additional
mathematical premise, source edit, or frozen-contract change is requested.
Approval of this plan does not certify that the uncompiled dependency copies
already constitute checked theorems.

## Source and interface checks

I reread the article's literal profile definition (TeX 699–745), representative
replacement and profile estimates (873–936 and 999–1036), and the old paper
2510.22783v1, Definition 4.7 and the profile enumeration at the end of the proof
of Proposition 4.2 (PDF pages 23 and 32–33; extracted text 1364–1383 and
1979–2027). The old profile records exceptional **pairs** `(t,x[t])`; the current
article at 722–724 records only exceptional **positions**. The proposed code
retains that distinction. Relevant Lean interfaces are `Digits.lean:17–63`,
`:176–186`, `:247–272`, `DigitEstimates.lean:16–31`, `:56–62`,
`Riffle/Words.lean:8–13`, `:138–176`, `:197–215`, and the checked
`BoundaryCounting.lean:193–240` and `Counting.lean:86–138`.

## P01 — approved

The proposed raw count is exactly the natural cardinality inside the existing
`digitCount` definition. Its defining fibre is a subset of `Fin K`, so it has
cardinality at most `K`, independently of endpoint order, legality, regularity,
or the sign of `chi`. The normalized identity is literal division by
`logScale N`; it remains an identity for `N = 0` or `N = 1` under Lean's
totalized real division, without an inverse-normalization inference.

The pair consisting of the count function and the exceptional-position finset
is the literal source data. Equality of such pairs is exactly the conjunction
in `SameCoarseProfile` when all common parameters, including endpoints, are
fixed. No equality of exceptional digit labels is part of this equivalence.

T06's `sourceExceptionalPositions` and the existing definition use the same
clipped `positions K v M` and the same negated `IsGoodDigit` filter. Substituting
arbitrary word-dependent endpoints pointwise preserves this equality. Empty
windows and endpoints beyond `K` require no added order premise.

## P02 — approved

Write `d = R * P.cellCount * k`. The finite code type can be

`SparsePattern K h k × ((Fin R × Fin P.cellCount × Fin k) → Fin (K+1))`.

Its cardinality is exactly `lowCount K h k * (K+1)^d`. For every realized datum,
the first component is its actual exceptional set, together with the selected
word's digits restricted to that set. The second component consists of its
raw counts, bounded by P01. Decoding forgets the exceptional labels and divides
the counts by the common `logScale N`. Every actual datum therefore belongs to
the decoded range. Decoding need not be injective; arbitrary invalid count
arrays or incompatible sparse data only enlarge this finite cover.

This proves finiteness of the actual image before its `Nat.card` bound. The
index type `I` need not be finite, countable, or decidable, and no finite-domain
instance should be added to it. A finite cover of its image is sufficient.
This order matters because a bare `Nat.card` inequality for an unproved-finite
type could be vacuous. The predicate `Q` only restricts the image, and the
sole additional hypothesis on selected indices is the stated exceptional
cardinality bound.

The `k = 0` case is sound without a default digit. If `K > 0`, the existence of
a selected full word is impossible. If `K = 0`, all actual exceptional sets are
empty, all count arrays have their unique zero values, and the bound is one.
Labels on an empty set require no inhabitant of `Fin 0`. Similarly, zero time
or spatial-key dimensions introduce no need for nonempty index types. The
candidate's stated `N ≥ 2` is retained; no stronger normalization assumption
is needed. No regularity, legality, endpoint ordering, or full support is used.

## P03 — approved

The actual admissible-pair subtype is finite by T05. It has cardinality at most

`[D.k * (D.K+1) * lowCount D.K (floor (boundaryThreshold A)) D.k]^2`.

P02 applies to the possibly infinite input type consisting of such pairs,
full indices, and natural endpoints, with the stated selection predicate and
exceptional-cardinality restriction. The image of pair-and-data lies inside
the product of the actual pair subtype and the finite coarse-data image.
Multiplying their bounds and collecting `(D.K+1)` powers gives exactly the
candidate exponent `R*P.cellCount*D.k+2`. The final-digit and length factors
needed for terminal and empty boundary cases are already present in T05.

Variable endpoints and repeated extensions do not contribute extra factors:
the theorem counts the resulting image, not its preimages. `FullIndex D`
contains all digit functions, including illegal ones, which is a permissible
counting cover. Imposing legality on this entire counting domain would add an
unrequested premise. Here `D.k ≥ 2` is already a field consequence of `Model`,
not a new assumption on P02.

For the source-prefix consequence, `Legal D x` gives `|x| ≤ D.K` and the
existing `full_extension` gives a legal full list extending `x`.
`fullList_of_full` converts that list into a full index. If two full indices
extend the same `x`, `digit_prefix` and `fullList_digit` imply equality of
their digit values at every `j < |x|`. Every position examined by the profile
at `v=|join y z|`, `M=|x|` has precisely this property. Consequently their good
sets, exceptional sets, raw count fibres, and normalized coarse data coincide.
The join-prefix assumption gives `v ≤ M`; it is already among the proposed
source-family premises. Existence of an extension is a derived fact, never an
extra source-family hypothesis.

The required inclusion must count source **data** from each triple using this
extension independence. It must not count all full extensions as distinct
prefixes: at `M < D.K` such a count contains an unused suffix factor. The
candidate explicitly avoids that previous trap. Actual retained/stable-prefix
applications still must supply their existing legality and join-prefix facts;
no stopping-rule or fluctuation statement follows just from this image bound.

## P04 — approved with the exact existing binders

The exact `profile_cost_replacement` statement has `N ≥ 2`, `chi > 0`, `C ≥ 0`,
`P.IsRegular chi C`, `w ≤ v`, `v ≤ M`, `M ≤ K`, and `LegalPrefix p x M`.
All of these remain in the exported source consequence, including premises
that an individual proof step might not require. Both bounds must remain:
the one with the actual good-position cardinality and the coarser one with
`M-v`. The latter uses `C*chi ≥ 0` and the exact interval-cardinality formula,
so its proof must retain the displayed endpoint domain.

The finite regrouping identity gives
`S = (sum over good positions of representative digitCost)/logScale N`.
The defining `Q` is the actual exceptional cost sum. Splitting the actual
position interval and regrouping by `digitKey` gives precisely the F04–F06
finite forms. Good-coordinate cost comparison comes from the existing
regularity clause; positivity of unused representative coordinates is neither
necessary nor available. This does not equate the actual ambient length `w`
with a rounded effective time. The source's later integral approximation is
not needed for this exact finite decomposition and is not proved by it.

## P05 — approved with distinct theorem domains preserved

The exact D11 domain is `N ≥ 2`, `chi > 0`, and `theta ∈ [3,4]`, with arbitrary
endpoints and time classes. A positive good count entails a representative
coordinate larger than `2*chi`, hence positive. This is precisely the support
condition needed by finite Gibbs. Coordinates with zero count are omitted;
an all-zero cell contributes zero. No full-support, regularity, or legality
hypothesis may be added to D11.

The source entropy formula in `profileH_source_formula` is a separate existing
theorem. Its existing additional `chi > 0`, regularity, and `LegalPrefix`
binders must remain when reused, even though the finite algebra could support
a broader theorem. Those extra binders must not be propagated backwards as
requirements of D11. Its zero-total branch is necessary for empty windows and
unused cells.

The exact `exceptional_psi_error` domain is `k ≥ 2`, `N ≥ 2`, and
`theta ∈ [2,4]`; it has no positive-chi, regularity, legality, or endpoint-order
premise. Its difference is exactly the exceptional-position sum of the
representative `psi`, divided by `logScale N`. Applying
`0 ≤ psi ≤ 4*log k` positionwise gives the stated interval with
`profileR = exceptionalCard/logScale N`. Summing by positions retains every
cell multiplicity without introducing a spurious partition-size factor.
No equality to an integrated time-profile term is asserted.

## Exact dependency proof-compatibility repairs — approved

The reviewed original files have SHA-256:

- `Analysis.lean`: `6cb844a02817905bc2e87f57277b23e68c2040dd2b1be6509d4b4320eeb3ac30`.
- `Digits.lean`: `003eaf611730d63c89ed9363454af2f5d35709efaf34122f94a10ec509f9609e`.
- `DigitEstimates.lean`: `e7a434c6aaaa1d5c32bfcfc1e26fd8bfe48d1be6ee0e0dcc34bec75375b8f9dd`.

I inspected the original read-only test log at
`/private/tmp/riffle-profile-source-review/RiffleTimeProfile/Analysis.log`.

1. At Analysis 111–113, append `ring` after the existing `field_simp` in the
   local cancellation proof. The log's remaining goal is exactly a polynomial
   rearrangement. The needed nonzero denominators follow from the already
   available `hl : 0 < c l` and `hZ : 0 < Z`. This changes neither the Gibbs
   theorem domain nor its zero-count branch.
2. At Analysis 150, replace `continuous_finsetSum` by
   `continuous_finset_sum`. The pinned declaration is the additive theorem
   generated by `@[to_additive]` from `continuous_finset_prod` in
   `Mathlib/Topology/Algebra/Monoid.lean:845–848`. Its finite-index continuity
   premise matches the following `intro l _` proof exactly. This is a library
   spelling change, not a new continuity assumption on the time law.
3. At Analysis 239, replace `let : Fintype I := Fintype.ofFinite I` by
   `letI : Fintype I := Fintype.ofFinite I`. Here `I = Set.range raw` is a
   subtype of the finite function type `Fin k → Fin m`; its finiteness is
   already available. The local instance exposes that existing finiteness to
   `Fintype.card` and `Fintype.equivFin`; it does not assume the index type of
   P02 is finite.

This approval covers only these exact proof-local repairs. It does not approve
unseen follow-up edits, changes to theorem headers or definition bodies, or
edits to originals or the already checked Base/Ambient copies. The complete
dependency copies still must compile and have their foundations checked before
their declarations are treated as proved project dependencies.

## Adversarial scope boundary

A small exceptional-profile collision explains why the distinctions above
matter. At one exceptional position with two different positive selected
probabilities, the two digit choices have the same zero good-count array and
the same singleton exceptional-position set. Their exceptional costs differ.
Thus coarse data do not determine `Q` or exact `cL`, and their word fibre need
not have the size of one labelled multinomial fibre. The detailed source-valid
counterexample remains in `reviews/counterexamples.md`.

P01–P05 do not assert any of those false identifications. They also do not solve
the time-kernel measurability, interval-integral approximation, effective-time
rounding, or remaining profile-class contribution obligations. They provide a
legitimate finite source-data bridge within their explicitly stated scope.
