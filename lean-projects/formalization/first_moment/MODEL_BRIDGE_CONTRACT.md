# Actual boundary encoding: supplemental contract

Status: FROZEN. Three independent reviewers approved all seven definitions and B1–B7 before any Lean implementation of this bridge.

This is a deterministic application of the already frozen profile counting interface to the newly supplied stable-block definitions. The original 29 interfaces and `FROZEN_CONTRACT.md` remain unchanged. No model assumption is added: the data are exactly `D : Riffle.Model`, `A : Riffle.Setup D`, and, for a single boundary, `s : Riffle.Side`. The mathematical sources remain the three user-authorized files.

The namespace is `InhomogeneousShuffle.FirstMoment.Model`; the implementation will be separate from the original modules, in `FirstMomentModel/BoundaryEncoding.lean`. It may use the proved `Riffle.Boundary` imports, the frozen `FirstMoment.Counting` results, and trusted mathlib. No unproved declaration or new project axiom is permitted.

## Definitions

All definitions below have implicit `D` and explicit `A`, and have no extra model hypotheses.

1. `boundaryBudget A : Nat` is the natural floor of `A.C / Real.log (1 / A.chi) * Real.log (D.N : Real)`, exactly the existing real admissibility threshold.
2. `outward A s x i : Prop` is `digit x i < leftIndex A i` for the left side, and `rightIndex A i < digit x i` for the right side. It is the same predicate used in `Riffle.violations`.
3. `boundaryPositions A s x : Finset (Fin D.K)` contains exactly the indices `i` with `A.w.length <= i.val`, `i.val < x.length`, and `outward A s x i.val`. In particular, it includes an outward final digit in a no-crossing fallback.
4. `boundaryTag A s` maps the subtype `{x : Riffle.Word // x in Riffle.Admissible A s}` to `Fin (D.k+1)`. If `A.w.length < x.length` and `Cross A s x (x.length-1)`, its value is the actual last digit. Otherwise its value is the sentinel `D.k`. A genuine crossing at length `D.K` therefore retains its digit; length `D.K` alone does not select the sentinel.
5. `encodeBoundary A s` maps that same admissible subtype to the existing `BoundaryCode D.K D.k (boundaryBudget A)`. Its three fields are the length, `boundaryTag`, and the sparse assignment consisting of `boundaryPositions` with the actual digit at each recorded index. Length and digit bounds come from legality; the sparse budget comes from the existing admissibility inequality.
6. `decodeBoundary A s` maps every `BoundaryCode D.K D.k (boundaryBudget A)` to a `Riffle.Word`. Its length is the stored length. At each position below that length, in this priority order, it uses: the ambient digit if the position is before `A.w.length`; the stored sparse digit if the position belongs to the sparse support; the stored tag if this is the final position and the tag is less than `D.k`; otherwise the fixed `leftIndex A i` or `rightIndex A i`. Arbitrary codes are not asserted to decode to legal or admissible words.
7. `encodePair A` maps `{p : Riffle.Word × Riffle.Word // Riffle.AdmissiblePair A p.1 p.2}` to the product of two `BoundaryCode D.K D.k (boundaryBudget A)` types by applying `encodeBoundary A .left` and `encodeBoundary A .right` in that order. The existing compatibility condition stays in the source subtype.

The original `BoundaryCode`, `SparseAssignment`, and all stable-block definitions are used literally and are not redefined.

## Exhaustive theorem interfaces

The following seven theorem interfaces are the complete supplemental list. Proof-local intermediate facts are permitted; no new exported theorem is to be introduced without its own prior review and freeze.

B1. `boundaryPositions_card`: for every word `x`, the sole explicit hypothesis `x.length <= D.K` implies `(boundaryPositions A s x).card = Riffle.violations A s x`. No legality, nonterminal, or positivity premise is needed for this finite support transport.

B2. `admissible_violations_le_budget`: for every word `x`, the sole explicit hypothesis `x in Riffle.Admissible A s` implies `Riffle.violations A s x <= boundaryBudget A`. No independently assumed integer budget or sign condition is allowed.

B3. `decode_encode_boundary`: for every `x : {x : Riffle.Word // x in Riffle.Admissible A s}`, `decodeBoundary A s (encodeBoundary A s x) = x.val`.

B4. `encodeBoundary_injective`: `Function.Injective (encodeBoundary A s)`.

B5. `admissible_boundary_card_le`: without a `Finite` or `Fintype` premise on the source subtype,

`Nat.card {x : Riffle.Word // x in Riffle.Admissible A s} <= (D.K+1)*(D.k+1)*sparseCount D.K D.k (boundaryBudget A)`.

B6. `encodePair_injective`: `Function.Injective (encodePair A)`.

B7. `admissible_pair_card_le`: without a `Finite` or `Fintype` premise on the source subtype,

`Nat.card {p : Riffle.Word × Riffle.Word // Riffle.AdmissiblePair A p.1 p.2} <= ((D.K+1)*(D.k+1)*sparseCount D.K D.k (boundaryBudget A))^2`.

No retention, positive fluctuation, local-good, asymptotic horizon, or nonterminal premise occurs in B1–B7. Finiteness follows from the proved injection into an existing finite code type. These theorems do not assert that all stable words inject into `ProfileKey`; distinct good-digit rearrangements can intentionally share a profile class.

## Review comparison and verification requirements

The algebra reconstruction, Lean statement design, and adversarial audit independently found the same reconstruction. They agree on the exact natural floor conversion, inclusion of all outward positions, and the guarded crossing tag. They checked crossing at the last column, terminal fallback, empty ambient prefix, terminal ambient prefix, `K=0`, and zero piles. They identified no missing model hypothesis. A tag based merely on `length < K`, or a sparse support omitting the final fallback digit, would be incorrect and is excluded by these definitions.

All three reviewers approved the exact proposed document before this status was frozen; `MODEL_BRIDGE_FREEZE.json` records the reviewed draft hash, frozen contract hash, reviewer reports, source hashes, and time. All seven results must compile and pass a dependency audit permitting only the standard Lean foundations. The original 29-theorem audit remains separate and must still pass without any change to its frozen interfaces.
