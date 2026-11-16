# LB11 completed-input integration acknowledgement v1

INTEGRATED_COMPLETED_INPUT. The exact frozen theorem is proved and registered:

```lean
RiffleLowerV2.MacroscopicLower.macroscopicIntegrable :
  RiffleLowerV2.Targets.MacroscopicIntegrableTarget
```

Import `RiffleLowerV2.MacroscopicLower.Main`. The derived `macroscopicIntegrable_tendsto` is also a checked theorem. Both sources rebuilt without diagnostics using `python3 build.py RiffleLowerV2.MacroscopicLower.Main`; see `LB11_integration_build_v1.log` and its immutable provenance JSON. The fresh warnings-as-errors `LB11_integration_audit_v1.log` matches all 17 compiled records exactly, with only `Classical.choice`, `Quot.sound`, `propext` in the axiom union.

All 47 input/source/audit hashes and three independent final reviews were validated. The coordinator's source review is `LB11_integration_review_v1.md`. Recheck registration with `python3 scripts/check_dependency_receipt.py LB11-v1`.

Registry manifest: `Contracts/dependencies/LB11-v1/SHA256.json`, SHA-256 `2f13fc82ec167cff156a3304096450bdcd4e686ab43dbb465cd66b4230b1239c`. Completed lane receipt SHA-256: `e98aa6b4c423d27c4c3b7c4dbfb62cc0e3993582cc5f2908f0a6c02cb6ae34f8`. Original frozen manifest SHA-256: `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`.

Ledger v10 certifies all 58 frozen exports and both E and explicitly scalar-integrable M. M retains integrability of the chosen partition's cell masses, a, and psi for alpha in [2,4], with the same P in AlmostLike and the scalar premise. It does not certify the historical arbitrary-TimeLaw endpoint. All original contracts, lane sources, umbrella files and old records remain unchanged. The separate fresh package build and LB12 final audit are still to be recorded.
