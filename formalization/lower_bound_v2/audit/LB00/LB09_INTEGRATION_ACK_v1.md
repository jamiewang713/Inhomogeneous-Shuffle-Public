# LB00 integration acknowledgement: completed LB09 v1

**INTEGRATED_COMPLETED_INPUT**, recorded 2026-10-01T17:33:52.920376+00:00.

Downstream import: `RiffleLowerV2.Localization.Main`. It is registered as a completed input for LB10/LB11. All five frozen LB09 exports are proved and available in the coordinator overlay:

| Required theorem | Exact frozen type |
|---|---|
| `RiffleLowerV2.Localization.relativeEndpoint` | `RiffleLowerV2.Targets.RelativeEndpointTarget` |
| `RiffleLowerV2.Localization.deterministicColdGeometry` | `RiffleLowerV2.Targets.DeterministicColdGeometryTarget` |
| `RiffleLowerV2.Localization.localization` | `RiffleLowerV2.Targets.LocalizationTarget` |
| `RiffleLowerV2.Localization.coldGeometryFromEmpirical` | `RiffleLowerV2.Targets.ColdGeometryFromEmpiricalTarget` |
| `RiffleLowerV2.Localization.lB09` | `RiffleLowerV2.Targets.LB09Target` |

The coordinator verified `audit/LB09/COMPLETION_RECEIPT_v1.json`, SHA-256 `8f7a4edb9be295714bb37056aba3d507af8a8febbfa880cf8b32248e3ef02d4f`, all 28 recorded source hashes and all 22 audit hashes before and after compilation. The source and import manifests agree with the files. Every final component review's source table matches, as do the historical-source and adapted-source provenance records. The approved LB09-v1 dependency receipt passes; registered pinned-library sources match their pinned commits. The original manuscript and frozen v1 contract remain unchanged.

`python3 build.py RiffleLowerV2.Localization.Main` rebuilt the 26-module implementation closure with Lean 4.33.1 and pinned mathlib, returning BUILD_OK without warnings or errors. The separately recorded Endpoints/Check.lean and Geometry/Check.lean diagnostic sources are hash-bound but outside Main. Immutable evidence: `audit/LB00/LB09_integration_build_v1.log` and `LB09_integration_build_provenance_v1.json`.

The unchanged `audit/LB09/Check_v1.lean` passed with warnings treated as errors against only coordinator outputs. All five required entries are actual theorem declarations whose types are exactly the frozen target constants. All 293 elaborated declaration records match the final lane inventory; all 160 public records match after excluding source-location metadata. Every transitive closure uses only propext, Classical.choice and Quot.sound. Evidence: `audit/LB00/LB09_integration_audit_v1.log` and `LB09_integration_declarations_v1.json`. This final audit includes the additive polynomial-envelope corollary omitted from the historical 292-declaration component snapshot.

The additional theorem `RiffleLowerV2.Localization.coldLocalization_failure_le_envelope` bounds actual localization failure by

`2*(T+1)*N^(1+T*log k)*exp(-N^(kappa eta/4)/8)`.

Its complete elaborated type and closure are in the registry and declaration inventory. It retains its explicit finite geometry, depth and scalar-threshold hypotheses; the final frozen localization theorem discharges these threshold conditions uniformly.

All five final independent component reports and their resolution were read, with authorship boundaries preserved. They cover endpoints, geometry, finite intervals/probability, bridge/rank barriers and final event/empirical assembly. Source correspondence is `lem:cold-geometry`, `lem:finite-relative-endpoints` and `lem:localization`. No unresolved finding remains in those reports.

The actual empirical tilt inequality supplies six-kappa entropy slack before type perturbation. Geometry constructs the classes, bridge/reserves and literal integer union, retains chiGood² and all ceiling/bridge-deletion costs, and proves the exact cardinality, mass, exponent, digit and boundary bounds. The endpoint theorem retains the right ambient fluctuation and its N=0/empty-suffix domain. One actual allPrefixEvent(kappa/4) controls endpoints and reserves for every tail, with two units of rank slack. The first-two-copies edge assignment is proved injective after actual localization is established.

Cutoff xi and its regular partition precede N0, and empirical assembly chooses them before epsilon. Every threshold precedes cuts, witness, geometry, selected words and samples. The final empirical theorem constructs both witness and geometry and removes the stochastic-event premise. Optional LB01 reuse is confined to the approved deterministic Model.Sorting module; no physical-law or graph-mixture assumption enters this proof.

Completed registry: `Contracts/dependencies/LB09-completed-v1/SOURCES.json`. Immutable manifest SHA-256: `4035b8e4047b34ef3499c873c16a06ccf8355812d42aa5ef609cc6a958904873`. `python3 scripts/check_dependency_receipt.py LB09-completed-v1` passes and binds the prior LB09-v1 authorization and completed upstream evidence. Downstream lanes should use this check alongside their unchanged frozen readiness checks. Registration of this input does not by itself certify every downstream prerequisite or theorem.

The additive ledger `audit/LB00/INTEGRATION_LEDGER_v7.md` and `.json` records 48 of 58 frozen exports certified: LB01–LB06, LB08 and LB09. E, integrable M and the historical arbitrary-TimeLaw endpoint remain uncertified. All lane sources, old audits, contract freezes, shared definitions, ownership, configuration and umbrellas were preserved. No LB10/LB11 proof work was started by this integration.
