# Actual admissible-boundary encoding: candidate interface

Status: independently reviewed statement design, 2026-09-17. No new statement is frozen by this report; no Lean implementation or original first-moment interface was changed. The mathematical source read was the authorized unified TeX, specifically the boundary definitions and the boundary/profile counting argument. Implementation dependencies were checked only in the existing project Lean and trusted mathlib sources.

The proposed seven definitions and seven theorems are viable with **no new model hypotheses**. They encode the actual `Riffle.Admissible` subtype, rather than a hypothetical family supplied with an extra integer budget assumption.

Suggested module: `FirstMomentModel/BoundaryEncoding.lean`.
Suggested namespace: `InhomogeneousShuffle.FirstMoment.Model`.
In all signatures below, `D : Riffle.Model`, `A : Riffle.Setup D`, and `s : Riffle.Side`. The existing `BoundaryCode`, `SparseAssignment`, and `sparseCount` are those already frozen in `InhomogeneousShuffle.FirstMoment`.

## Exact definitions

1. `boundaryBudget (A : Riffle.Setup D) : ℕ` is

   `Nat.floor (A.C / Real.log (1 / A.chi) * Real.log (D.N : ℝ))`.

   This is the source cutoff rounded down. It is not a new parameter or hypothesis.

2. `outward (A : Riffle.Setup D) (s : Riffle.Side) (x : Riffle.Word) (i : ℕ) : Prop` is exactly

   * left: `Riffle.digit x i < Riffle.leftIndex A i`;
   * right: `Riffle.rightIndex A i < Riffle.digit x i`.

3. `boundaryPositions (A : Riffle.Setup D) (s : Riffle.Side) (x : Riffle.Word) : Finset (Fin D.K)` is `Finset.univ` filtered by

   `A.w.length ≤ i.val ∧ i.val < x.length ∧ outward A s x i.val`.

4. `boundaryTag (A : Riffle.Setup D) (s : Riffle.Side)
   (x : {x : Riffle.Word // x ∈ Riffle.Admissible A s}) : Fin (D.k + 1)` is the last digit as an element of `Fin (D.k + 1)` precisely when

   `A.w.length < x.val.length ∧ Riffle.Cross A s x.val (x.val.length - 1)`.

   Otherwise it is `Fin.last D.k`, whose value `D.k` is the sentinel. The legality supplied by boundary membership proves that a recorded crossing digit is strictly below `D.k`.

5. The encoder has exact type

   ```lean
   encodeBoundary (A : Riffle.Setup D) (s : Riffle.Side) :
     {x : Riffle.Word // x ∈ Riffle.Admissible A s} →
       BoundaryCode D.K D.k (boundaryBudget A)
   ```

   Its entries are: the absolute length in `Fin (D.K + 1)`; `boundaryTag A s x`; and the sparse assignment with support `boundaryPositions A s x.val` and label at position `i` equal to `Riffle.digit x.val i.val`, represented in `Fin D.k`. The support bound comes from B1 and B2 below. The digit bound comes from `Riffle.Legal`.

6. The decoder has exact type

   ```lean
   decodeBoundary (A : Riffle.Setup D) (s : Riffle.Side) :
     BoundaryCode D.K D.k (boundaryBudget A) → Riffle.Word
   ```

   It is total on this code type. No legality claim is made for an arbitrary code. Write a code as `(length, tag, (Q, labels))`, with `ell := length.val`. Construct a list of length `ell` by `List.ofFn`. For each position `i < ell`, use the following ordered cases:

   1. If `i < A.w.length`, return the ambient digit `Riffle.digit A.w i`.
   2. If the corresponding `j : Fin D.K` belongs to `Q`, return `(labels ⟨j, membership⟩).val`.
   3. If `i + 1 = ell` and `tag.val < D.k`, return `tag.val`.
   4. Otherwise return `Riffle.leftIndex A i` or `Riffle.rightIndex A i`, according to `s`.

   The index `j : Fin D.K` exists because `i < ell ≤ D.K`, with the latter bound supplied by `length : Fin (D.K + 1)`. A decoder parameterized by an arbitrary additional `qb` would also be valid, but is unnecessary for the proposed interface.

7. The pair encoder has exact type

   ```lean
   encodePair (A : Riffle.Setup D) :
     {p : Riffle.Word × Riffle.Word //
       Riffle.AdmissiblePair A p.1 p.2} →
       BoundaryCode D.K D.k (boundaryBudget A) ×
         BoundaryCode D.K D.k (boundaryBudget A)
   ```

   It applies `encodeBoundary A .left` and `encodeBoundary A .right` to the respective words and admissibility proofs extracted from the pair. Compatibility is present in the actual source subtype; the map need not encode that proof separately.

The helper definitions `outward` and `boundaryTag` could technically be inlined, but retaining the proposed list makes the match with the source and with `Riffle.violations` explicit. No additional public definitions are needed.

## Exact theorem signatures

The following are proposed statements only; their proof bodies are intentionally not implementation work in this report.

```lean
theorem boundaryPositions_card (A : Riffle.Setup D) (s : Riffle.Side)
    (x : Riffle.Word) (hx : x.length ≤ D.K) :
    (boundaryPositions A s x).card = Riffle.violations A s x

theorem admissible_violations_le_budget (A : Riffle.Setup D)
    (s : Riffle.Side) {x : Riffle.Word}
    (hx : x ∈ Riffle.Admissible A s) :
    Riffle.violations A s x ≤ boundaryBudget A

theorem decode_encode_boundary (A : Riffle.Setup D) (s : Riffle.Side)
    (x : {x : Riffle.Word // x ∈ Riffle.Admissible A s}) :
    decodeBoundary A s (encodeBoundary A s x) = x.val

theorem encodeBoundary_injective (A : Riffle.Setup D) (s : Riffle.Side) :
    Function.Injective (encodeBoundary A s)

theorem admissible_boundary_card_le (A : Riffle.Setup D) (s : Riffle.Side) :
    Nat.card {x : Riffle.Word // x ∈ Riffle.Admissible A s} ≤
      (D.K + 1) * (D.k + 1) * sparseCount D.K D.k (boundaryBudget A)

theorem encodePair_injective (A : Riffle.Setup D) :
    Function.Injective (encodePair A)

theorem admissible_pair_card_le (A : Riffle.Setup D) :
    Nat.card {p : Riffle.Word × Riffle.Word //
      Riffle.AdmissiblePair A p.1 p.2} ≤
      ((D.K + 1) * (D.k + 1) *
        sparseCount D.K D.k (boundaryBudget A)) ^ 2
```

These are B1–B7 in the order proposed by the root reviewer. In particular, B1 does not need legality or boundary membership, only the stated length bound. B2 needs only actual admissible membership. B5 and B7 do not take `Finite`, `Fintype`, positivity, or integer-budget assumptions.

## Reconstruction and edge cases

Before the first crossing, the source left-boundary condition says `digit ≤ leftIndex`. If the position is not outward, it also says `leftIndex ≤ digit`, so the digit is exactly `leftIndex`. The right case reverses these inequalities. Thus the positions not explicitly stored in the sparse set or final tag are determined by the fixed model and side.

At a genuine final crossing, the digit is inward, so it cannot also be outward. Consequently, the decoder's sparse-position branch does not hide the crossing tag. In the fallback case there is no crossing at any column after the ambient word; outward digits are stored, including a possible outward digit at the final column, and all other digits equal the side boundary.

The source cases are handled exactly:

* **First crossing before `K`:** the final crossing digit is recorded.
* **First crossing at `K`:** the final crossing digit is still recorded. Using `x.length < K` as the tag test would be wrong.
* **Terminal fallback at `K`:** the sentinel is recorded. The final digit may be an outward digit and then is recovered from the sparse set.
* **Ambient prefix already has length `K`:** the boundary word is the ambient word; the crossing test includes `w.length < x.length`, so the tag is the sentinel. Every decoded digit comes from the ambient prefix.
* **`K = 0`:** the legal ambient and boundary words are empty; the code length and support are empty, and decoding produces the empty list. No new `0 < K` assumption is needed.
* **First possible column after the ambient word:** this position is included in the support and crossing rules. No first-column exclusion is introduced.

The side and ambient word are fixed parameters of the encoder/decoder. The code need not store them. The two components of `encodePair` distinguish left from right; there is no proposed injection of a varying side into a single side-free code space.

## Existing finite structures and proof dependencies

`Riffle.Word` is `List ℕ`, so it is not itself finite. `Riffle.Legal` already supplies the length and digit bounds needed for these encodings. The package has no existing finite instance for all admissible prefixes.

`Riffle.FullIndex D := Fin D.K → Fin D.k` is finite. `Riffle.fullList_injective`, `Riffle.fullList_existsUnique`, and `Riffle.fullList_of_full` relate it to full words, but these concern full length `K` and are not needed to encode shorter boundary words. A separate bounded-prefix universe would be possible but is unnecessary: the boundary-code injection itself proves finiteness.

The frozen `SparseAssignment` has its finite instance and exact cardinality theorem `InhomogeneousShuffle.FirstMoment.card_sparseAssignment`. Thus `BoundaryCode` is finite by products. Its cardinality is exactly

`(K+1) * (k+1) * sparseCount K k qb`.

After B4, `Fintype.ofInjective (encodeBoundary A s) (encodeBoundary_injective A s)` constructs the actual finite instance for the admissible subtype. The analogous construction applies after B6 to admissible pairs. B5/B7 can use these as local instances, `Nat.card_eq_fintype_card`, and `Fintype.card_le_of_injective`. Equivalently, trusted `Finite.card_le_of_injective` applies directly. Hence the use of `Nat.card` is backed by proved finiteness, not its default value on an infinite type. No public instance declaration or additional finiteness theorem is required by the proposed list.

Relevant existing project theorems are `Riffle.admissible_mem_boundary`, `Riffle.boundary_mem_desc`, and `Riffle.digit_prefix`. The full disjunction in `Boundary`/`BoundaryCut` is used for reconstruction: `Riffle.boundary_nonterminal` alone is insufficient because it excludes terminal first crossings. `List.ext_getElem` and the `List.ofFn` element/length facts give equality with the decoded word. Injectivity then follows by applying the decoder and using `Subtype.ext`, avoiding equality manipulations between dependent sparse-label functions.

B1 is a finite reindexing between the existing natural-index violation set and its `Fin K` copy. B2 follows directly from `Nat.le_floor` applied to the real inequality stored in admissible membership. It therefore does not need a separately assumed nonnegative cutoff. For later asymptotic use, `boundaryBudget A ≤` the real source cutoff follows from `Nat.floor_le` and the already present `Setup` positivity facts; this can remain proof-local to that later application.

## Remaining scope after B1–B7

These interfaces close the actual **boundary** encoding and pair count. They do not assert that full profile-class data have already been encoded into `ProfileKey`. That later map must still supply extension length, bounded count vector, labeled exceptional positions, and routing, and prove that equal keys mean equal source classes. The existing frozen `profile_card_le_of_injective` can then perform the final finite count. No stochastic localization or truncation-mass conclusion follows merely from B1–B7.
