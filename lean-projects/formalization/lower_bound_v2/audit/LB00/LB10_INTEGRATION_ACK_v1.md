# LB10 completed-input integration acknowledgement v1

Status: INTEGRATED_COMPLETED_INPUT. All five unchanged frozen targets are proved and available to downstream lanes. Empirical endpoint E is now coordinator-certified.

Registered import: `RiffleLowerV2.EmpiricalLower.Main`.

Exact compiled theorem exports:

```lean
RiffleLowerV2.EmpiricalLower.empiricalCombined : RiffleLowerV2.Targets.EmpiricalCombinedTarget
RiffleLowerV2.EmpiricalLower.coldOnly : RiffleLowerV2.Targets.ColdOnlyTarget
RiffleLowerV2.EmpiricalLower.manyEdges : RiffleLowerV2.Targets.ManyEdgesTarget
RiffleLowerV2.EmpiricalLower.finiteLargestWordTV : RiffleLowerV2.Targets.FiniteLargestWordTV
RiffleLowerV2.EmpiricalLower.largestOnly : RiffleLowerV2.Targets.LargestOnlyTarget
```

The coordinator rebuilt all eight implementation modules with `python3 build.py RiffleLowerV2.EmpiricalLower.Main`; `audit/LB00/LB10_integration_build_v1.log` records BUILD_OK without warnings or errors. The immutable build provenance is `LB10_integration_build_provenance_v1.json`. Check_v1.lean was rerun against the shared output with warnings as errors: all 93 declaration records, including private helpers, exactly match the completed lane inventory. Axiom union: `Classical.choice`, `Quot.sound`, `propext`.

All 45 completion-receipt hashes, required upstream manifests and historical port sources match disk. Final independent reviews cover all eight sources. Their resolutions and the coordinator assembly inspection are recorded in `LB10_integration_review_v1.md`.

Recheck: `python3 scripts/check_dependency_receipt.py LB10-v1`.

Registry manifest: `Contracts/dependencies/LB10-v1/SHA256.json`
SHA-256: `9fe2f82ad8be2c67eaa6b7f9f9e51e833b234952cbc339b238eefa70bfd399da`.

Original frozen manifest SHA-256: `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`.
Completed lane receipt SHA-256: `31e3d965e7c72d967f889bfb76118c93be2faecd94b95f208a506e3e912b3033`.

Source correspondence: `prop:largest-prefix`, `lem:many-edges`, `lem:lalley`, `prop:cold-lower`. The actual chronological physical inverse law is used. The cold endpoint constructs witness/geometry and discharges localization, concentration and graph-law inputs. No TimeLaw or temporal regularity is assumed. The largest branch requires no local-good premise. All branch thresholds precede N and cuts, including cuts whose alternative changes with N.

Integration ledger v9 records 57 of 58 frozen exports, including empirical E. The sole remaining frozen target is scalar-integrable macroscopic M. The historical arbitrary-TimeLaw endpoint remains uncertified. No historical freeze, lane source or umbrella was changed.
