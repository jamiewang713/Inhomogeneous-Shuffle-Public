# T05 implementation coverage

Implemented the frozen T05 contract in `RiffleProfiles/BoundaryCounting.lean`, after reading `FROZEN_TRUNCATION_CONTRACT.md` and `TRUNCATION_REVIEW_COMPARISON.md`. The implementation imports the root agent's `RiffleProfiles.BoundaryTruncation`, the existing frozen `Counting` module, and mathlib's finite natural-cardinality API. It reuses `boundaryThreshold` and the existing `Riffle` boundary/admissibility definitions without modifying or duplicating them.

## Public declarations

| Declaration | Coverage |
|---|---|
| `RiffleProfiles.boundarySparseSupport` | The exact relative support: `t.val + 1 < x.length - A.w.length` and a violation at absolute coordinate `A.w.length + t.val`. |
| `RiffleProfiles.admissibleBoundaryDescriptor` | Explicit map from the actual admissible natural-word subtype into `BoundaryDescriptor D.K (Nat.floor (boundaryThreshold A)) D.k`. |
| `RiffleProfiles.admissibleBoundaryDescriptor_injective` | Full reconstruction proves the map injective. |
| `RiffleProfiles.admissibleBoundaryFinite` | A `Finite` instance on the actual admissible-word subtype, derived from the injection. |
| `RiffleProfiles.admissibleBoundary_card_le` | `Nat.card` of that subtype is at most `D.k * (D.K + 1) * lowCount D.K (Nat.floor (boundaryThreshold A)) D.k`. |
| `RiffleProfiles.admissiblePairFinite` | A `Finite` instance on `{yz : Word × Word // AdmissiblePair A yz.1 yz.2}`, derived from its injection into the two admissible-word subtypes. |
| `RiffleProfiles.admissiblePair_card_le` | `Nat.card` of the compatible admissible-pair subtype is at most the square of the same one-boundary bound. |

## Exact encoding and reconstruction

The length field is the relative extension length `|x|-|w|`, as an element of `Fin (D.K+1)`. For a nonempty extension the final field stores `digit x (|x|-1)`, including terminal fallback. For an empty extension it stores the fixed zero digit; the existing `D.two_le_k` supplies its alphabet bound. The sparse labels are precisely the actual digits at their shifted absolute positions and form the dependent function on the selected support required by frozen `SparsePattern`.

The support cardinality proof shifts each relative position by `|w|`, injectively embedding it into the actual violation set. The original admissibility inequality supplies `violations ≤ Nat.floor (boundaryThreshold A)` via `Nat.le_floor`. No positive-count, cardinality, or finite-word-space hypothesis is introduced.

Two private elementary facts extract absence of every pre-final crossing from either branch of the actual `BoundaryCut` definition and force an unrecorded pre-final digit to equal the appropriate extreme index. The reconstruction then treats the fixed ambient prefix, recorded pre-final violations, forced pre-final extreme digits, and the separately recorded final digit. Equality of relative lengths gives equality of total lengths, and list extensionality proves equality of the actual words. When the extension is empty, all existing digits belong to the common ambient prefix; there is no final-digit lookup into an empty extension.

The cardinality theorems first derive finiteness from the proved injections and then use frozen `boundaryDescriptor_card_le`. The pair map retains the exact `AdmissiblePair` subtype, including compatibility, while forgetting only its proof component. Its target is the product of the two actual admissible-word subtypes. No unrestricted natural-list or unused suffix count occurs.

All auxiliary facts have complete proofs within the reviewed T05 proof route. There are no added assumptions, axioms, `sorry`, `admit`, or placeholder theorem bodies.

## Validation

Executed from the workspace root:

`python3 lean_formalization/check_lean.py lean_formalization/RiffleProfiles/BoundaryCounting.lean`

The final compiler run exited with status 0 and no output under `warningAsError=true`, producing `BoundaryCounting.olean`. The initial dependency wait was resolved by the completed `BoundaryTruncation.olean`; subsequent corrections were only decidability elaboration and simplification of projected equalities. No mathematical statement changed during implementation.

The root agent can now include the public declarations and their dependency closure in the combined independent audit and kernel axiom report. This module proves T05 only; it makes no asymptotic profile-class claim and does not alter terminal truncation policy.
