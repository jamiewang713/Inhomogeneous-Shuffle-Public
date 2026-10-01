# LB00 integration acknowledgement: completed LB04 v1

**INTEGRATED_COMPLETED_INPUT**, recorded 2026-10-01T16:13:18.912585+00:00.

Downstream import: `RiffleLowerV2.Ascent.Main`. All ten frozen targets are proved and available in the coordinator overlay.

| Required theorem | Exact frozen type |
|---|---|
| `RiffleLowerV2.Ascent.componentConcentration` | `RiffleLowerV2.Targets.ComponentConcentration` |
| `RiffleLowerV2.Ascent.componentExpectation` | `RiffleLowerV2.Targets.ComponentExpectation` |
| `RiffleLowerV2.Ascent.uniformScan` | `RiffleLowerV2.Targets.UniformScan` |
| `RiffleLowerV2.Ascent.componentComparison` | `RiffleLowerV2.Targets.ComponentComparison` |
| `RiffleLowerV2.Ascent.uniformGraphScan` | `RiffleLowerV2.Targets.UniformGraphScan` |
| `RiffleLowerV2.Ascent.relativeOrderIndependence` | `RiffleLowerV2.Targets.RelativeOrderIndependence` |
| `RiffleLowerV2.Ascent.boundaryAscentProbability` | `RiffleLowerV2.Targets.BoundaryAscentProbability` |
| `RiffleLowerV2.Ascent.bernoulliMGF` | `RiffleLowerV2.Targets.BernoulliMGF` |
| `RiffleLowerV2.Ascent.leastSuccessfulTranslate` | `RiffleLowerV2.Targets.LeastSuccessfulTranslate` |
| `RiffleLowerV2.Ascent.componentConcentrationTwoSided` | `RiffleLowerV2.Targets.ComponentConcentrationTwoSided` |

The coordinator verified `audit/LB04/COMPLETED_INPUT_v1.json` SHA-256 `f1c2b261127846938ca4291fb8262af864b522c5875686f89829e856a7a08585` and every bound source/artifact before and after compilation. The approved LB01-v1/LB04-v1 dependency receipts pass. Only the authorized Model.GraphSorting/FiniteLaws project helpers are used; no unplanned first-stage proof dependency appears.

`python3 build.py RiffleLowerV2.Ascent.Main` rebuilt the twenty-module Main import closure with Lean 4.33.1 and pinned mathlib, returning BUILD_OK. The standalone RelativeOrder/Check.lean diagnostic is bound by the lane receipt but is not imported by Main. Log and immutable provenance: `audit/LB00/LB04_integration_build_v1.log` and `LB04_integration_build_provenance_v1.json`.

The unchanged lane Check_v1.lean then passed with warnings treated as errors against only coordinator outputs. All ten exact-type assignments passed; all 269 declaration records match the lane inventory exactly, and the 163 public records match their compiled contents. Every closure uses only propext, Classical.choice and Quot.sound. Audit evidence: `audit/LB00/LB04_integration_audit_v1.log` and `LB04_integration_declarations_v1.json`.

All four independent final reviews were read and their final source hashes checked. They cover exact relative-order counts, clipped expectation, analytic bounds/asymptotics, and concrete concentration/scan/selection/test assembly. The source keeps component-index parity, discharges mutual relative-order factorization, handles zero boundary counts before division, and retains every internal edge in partial components. Exact constants remain exp(-t²/M), 2 exp(-t²/M), and e/2+r/6-d. Arbitrary integer H0, strict success versus weak failure, graph-only measurable least choice, and N0 before N,H0,G remain unchanged.

Additional compiled exports include the exact natural relative-order fiber count, `chosenTranslate` and its measurability, `conditionalLalleyTest`, and `conditionalLalleyTendsto`. The latter two explicitly retain mixture-law and graph-success/geometry inputs. LB10 must discharge these for the actual shuffle; this receipt does not certify E or M.

New registry: `Contracts/dependencies/LB04-completed-v1/SOURCES.json`. Its immutable manifest SHA-256 is `86f951f89a3a6e9968aa5a7102cce83ec7b013276324964b9a2c52789c0060ab`. Run `python3 scripts/check_dependency_receipt.py LB04-completed-v1` before consuming the import, alongside LB01-v1 and LB04-v1; the new check passed. Frozen lane tools remain unchanged and do not automatically read later receipts.

The additive ledger `audit/LB00/INTEGRATION_LEDGER_v2.md` and `.json` now records LB01, LB04 and LB06 integrated: 19 of 58 frozen lane exports. All older ledger versions, source/contract freezes, ownership, umbrellas and lane files were preserved. No downstream proof work was started.
