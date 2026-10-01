# LB06 completion receipt v1

Status: **COMPLETE — exact frozen roundedType theorem proved.**

```lean
import RiffleLowerV2.Types.Main
#check RiffleLowerV2.Types.roundedType
-- RiffleLowerV2.Types.roundedType : RiffleLowerV2.Targets.RoundedTypeTarget
```

This completes the assigned source lemma `lem:type-estimates`. It does not claim completion of downstream lanes or the final lower-bound endpoint. The manuscript, original packages, shared definitions and all v1 freezes were preserved.

## Exact result and constants

The theorem covers k>=2, C>=0, T>0, 0<xi<1/(4k), every fixed cell count m, every regular partition P with that count, all finite cut arrays and arbitrary selected sets I with |I|<=T log N, and alpha in [2,4]. Constants and threshold are chosen before P, cuts, I and alpha.

Put B=log(1/xi). The implemented constants are

```text
Ctype(k,C) = 1 + 10C + 40C exp(C) + 99k^5,
Cround(k,m,T,xi) = kmB + 2
                    + m(2k+1)(log(T+1)+3) + log(2+TB),
N0 = ceil(exp(1)) + 2.
```

The exact named definitions are `typeConstant`, `roundConstant`, and `typeThreshold`. The source proof uses the equivalent decomposition `Ctype=1+C+truncationCostConstant+truncationEntropyConstant`. Both coefficients are proved positive. The threshold is universal; its proof gives log N>=1. `roundingRate_tendsto` proves that (log(log N)+1)/log N tends to zero. The separate Ctype*T*xi*log(1/xi) term remains a fixed approximation budget at fixed xi.

The constructed data use deterministic cumulative-floor integer counts and the least maximal integer mass bin. `TypeDataSpec` supplies exact totals, support and coordinate error, nonempty raw/selected classes, exact products of natural multinomial coefficients, the occupied-bin bound, global maximality and deterministic ties, J*,H*>=0, exact cardinality N^H*, and the strict lower/weak upper mass interval. Actual selected probabilities are at least xi. `TypeApproximation` supplies the sum of empirical cost and entropy errors with the constants above.

## Source correspondence and dependency ledger

| Source obligation | Checked declarations | Status |
|---|---|---|
| Common internal regular partition | `exists_type_partition` via canonical `TimeProfile.exists_regular_partition` | Proved; constant 1 independent of xi |
| Retained law, zeros and denominator | `retainedTilt_denominator_pos`, `retainedTilt_sum`, support/positivity lemmas | Proved throughout cutoff range |
| Omitted tilted mass/cost/entropy | `omittedTiltedSum_le`, `omittedTiltedCost_small`, `omittedEntropySum_bounds` | Proved; bounds 9k^5 xi², 12k^5 xi² B, 48k^5 xi² B |
| Representative/actual transfer | `retainedTilt_cost_transfer`, `retainedTilt_entropy_transfer` | Proved, no LB05 or macro input |
| Supported deterministic counts | `roundedCount`, `roundedCount_sum`, `roundedCount_zero`, `roundedCount_error_lt` | Proved; strict error <1 |
| Exact nonempty raw class | `roundedClass_nonempty`, `roundedClass_card` | Proved by finite equivalence counting |
| Lower and upper entropy error | `factorial_log_error`, `multinomial_log_entropy_error`, `roundedClass_entropy_error` | Proved independently of old upper bound |
| Deterministic largest mass bin | `leastMaxBin`, maximality/tie/nonempty/card-bound lemmas | Proved for all natural bin indices |
| Exact mass/exponent specification | `constructedTypeData_spec` | Proved, all abstract helper inputs discharged |
| Empty selected block | `empty_classes_card_one`, `massOn_empty`, `empty_exponents_zero` | Proved; unique empty word, mass 1, exponents 0 |
| Quantified error and rate | `finite_type_approximation`, `type_approximation_uniform`, `roundingRate_tendsto` | Proved |
| Frozen public export | `roundedType : Targets.RoundedTypeTarget` | Proved with exact quantifier order |

There are no pending LB06 proof obligations or assumed target conclusions. Generic count, support and approximation helper premises are discharged in the concrete construction/assembly. The full exact names and Lean types of all public declarations appear in [EXPORTS_v1.md](EXPORTS_v1.md); machine-readable types and dependencies are in public-exports-v1.json and compiled-declarations-v1.json.

## Verification and trust closure

From `formalization/lower_bound_v2`:

```text
python3 scripts/check_dependency_receipt.py LB06-v1
python3 scripts/lane.py LB06 --check-ready
python3 scripts/lane.py LB06 RiffleLowerV2.Types.Main
```

The additive dependency check and frozen readiness check passed. The complete private lane build passed without warnings: [main-build-dev02.log](main-build-dev02.log), ending `LB06 BUILD_OK`. This rechecked all 13 owned proof modules using only the designated LB06 output area. Every source in SOURCES_v1.json has a corresponding newer checked output.

The full compiled audit [Check_v2.lean](Check_v2.lean) ran with warnings treated as errors and succeeded: [compiled-audit-v2.log](compiled-audit-v2.log). It inspected all 287 new elaborated declarations, including private/generated helpers, verified the required export is a theorem with literal type `RiffleLowerV2.Targets.RoundedTypeTarget`, and checked every transitive axiom set. The union is exactly `propext`, `Classical.choice`, `Quot.sound`. No proof placeholder, custom axiom or native proof oracle enters the closure. There are 151 public exports, of which 127 are theorems; completion rests on the exact target, not those counts.

The first audit-script attempt used an incorrect qualified environment accessor and failed only in its final metadata check. The corrected separate v2 audit passed; both original script and failure log are retained. All proof sources already passed the complete lane build before that audit correction.

The canonical partition import and optional registered mathlib imports are documented in LB00's LB06_DEPENDENCIES_READY_v1.md. The proof uses only the canonical Analysis module for the partition existence wrapper; its factorial and counting arguments do not need Stirling or multinomial library imports. Read-only/adapted source provenance and original/output hashes are in [PROVENANCE_v1.md](PROVENANCE_v1.md).

## Independent review and downstream receipt

The mathematical, exact-representation and missing-hypothesis reviews were completed before proofs and compared in REVIEW_COMPARISON_v1.md. LB00 acknowledged the unchanged interface in `audit/LB00/LB06_INTERFACE_ACK_v1.md` before implementation, then supplied its separate additive dependency receipt. No contract change was needed.

Final independent implementation reviews approved counting/construction, truncation, mass bins and assembly, including current source hashes: counting-review-v1.md, truncation-review-v1.md, massbins-review-v1.md and assembly-review-v1.md. The analytical worker additionally reviewed WordEstimates/Rates in truncation-integration-review-v1.md. All substantive findings are resolved; the selected cumulative-floor construction and explicit finite remainder are documented.

Downstream lanes should import `RiffleLowerV2.Types.Main` and consume `RiffleLowerV2.Types.roundedType`; concrete deterministic data are exposed as `constructedTypeData` with `constructedTypeData_spec`. This receipt plus the exact export inventory and source manifest is the LB06 completed-input evidence. The coordinator owns copying/rebuilding this import into the shared overlay, umbrella imports and any global ledger update. LB06 changed none of those files. Other lanes and the final lower-bound theorem are outside this certification.
