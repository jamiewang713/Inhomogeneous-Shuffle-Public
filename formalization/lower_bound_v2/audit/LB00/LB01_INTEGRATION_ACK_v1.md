# LB-00 integration acknowledgement: completed LB-01 v1

Status: **INTEGRATED_COMPLETED_INPUT**. Recorded 2026-10-01T15:43:00.035091+00:00.

The coordinator independently rebuilt `RiffleLowerV2.Model.Main` and all seven imported Model proof modules from their exact released sources into `.build/lib/lean`. All eight required frozen targets are checked theorems, including the chronological physical-law bridge. Downstream lanes may import `RiffleLowerV2.Model.Main` from the coordinator overlay. This integration proves no lower-bound endpoint E or M and starts no downstream proof work.

## Registered inputs and immutable identities

- Lane completed-input receipt: `audit/LB01/COMPLETED_INPUT_v1.json`, SHA-256 `b7d703a14bdacec38a76e63e7c79474fb76d2303a235580d65c4d383cc9c2e76`.
- Base v1 manifest: `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`; every bound file and original external-source hash was verified unchanged.
- New additive registry: `Contracts/dependencies/LB01-v1/SOURCES.json`.
- New manifest: `Contracts/dependencies/LB01-v1/SHA256.json`, SHA-256 `3144d85b8d51329be36df3a86670509a3853cd67ada2371beef31e51fa7f58aa`.
- Compiler: Lean (version 4.33.1, arm64-apple-darwin24.6.0, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release); mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
- Mathematical correspondence: `lem:ub-graph-representation`, manuscript SHA-256 `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`.

All source files, review/audit artifacts and receipt hashes bound by the lane's completed receipt matched before and after compilation. The additive manifest also binds the corrected metadata and new coordinator build/audit records. No lane source, shared source, frozen umbrella, ownership inventory, old ledger, old audit or historical release was edited.

## Verified exports and status

| Exact export | Exact frozen type | Current status |
|---|---|---|
| `RiffleLowerV2.Model.columnIndependence` | `RiffleLowerV2.Targets.ColumnIndependence` | PROVED |
| `RiffleLowerV2.Model.graphRepresentation` | `RiffleLowerV2.Targets.GraphRepresentation` | PROVED |
| `RiffleLowerV2.Model.graphEventIdentity` | `RiffleLowerV2.Targets.GraphEventIdentity` | PROVED |
| `RiffleLowerV2.Model.physicalMatrixBridge` | `RiffleLowerV2.Targets.PhysicalMatrixBridge` | PROVED |
| `RiffleLowerV2.Model.inversionTV` | `RiffleLowerV2.Targets.InversionTV` | PROVED |
| `RiffleLowerV2.Model.rowRelabeling` | `RiffleLowerV2.Targets.RowRelabeling` | PROVED |
| `RiffleLowerV2.Model.stableTie` | `RiffleLowerV2.Targets.StableTie` | PROVED |
| `RiffleLowerV2.Model.prefixRanks` | `RiffleLowerV2.Targets.PrefixRanks` | PROVED |

The coordinator also confirmed theorem exports for `columnMarginal`, `matrix_multiset_expect`, `matrix_multiset_event`, `sampleRelabel_fiber_card`, `shuffle_componentSort_fiber_card_eq`, `stableSort_physicalPullback`, `physical_graph_representation`, and `physical_graph_event`, all under `RiffleLowerV2.Model`. Exact elaborated types and direct dependencies for all 162 Model declarations are in `audit/LB00/LB01_integration_declarations_v1.json`, matching the lane's inventory exactly.

The graph law uses the canonical fixed-count sample and the explicit independent uniform-permutation mixture. The full-multiset finite identities and factorial fibers are proved. The physical bridge uses the actual triangular sample equivalence and chronological inversion; it does not assert the false same-raw-sample identity. Frozen arbitrary-natural quantifiers and all degenerate cases remain unchanged. No law-identification hypothesis was added.

## Review, compilation and closure

The lane's three pre-proof reports and comparison, final independent representation review on final hashes, and separately reviewed physical implementation were inspected. The final representation reviewer authored Physical and explicitly excluded independent self-review of that module; its separate hypotheses-review record supplies that review. Earlier graph-review snapshots are retained as history, with the final source-hash review governing the released files. No remaining review finding or shared amendment is required by these records.

Successful coordinator command:

```text
python3 build.py RiffleLowerV2.Model.Main
```

It returned `BUILD_OK`; log: `audit/LB00/LB01_integration_build_v1.log`; immutable build provenance: `audit/LB00/LB01_integration_build_provenance_v1.json`. Only the eight Model modules were newly compiled. Dependency-cache mutation was serialized by the existing coordinator lock; no private lane outputs were copied into the coordinator cache.

The coordinator then reran the unchanged `audit/LB01/Check.lean` against only the coordinator overlay with the pinned compiler and warnings as errors. All eight exact-target assignments succeeded. All 162 declaration records, including types and dependency/axiom data, match the lane audit exactly. The transitive axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`. Log: `audit/LB00/LB01_integration_audit_v1.log`.

The historical `audit/LB01/VERIFICATION_v1.json` copied eight PENDING strings from the original ownership inventory. The lane supplied additive `VERIFICATION_v2.json` and `VERIFICATION_STATUS_ADDENDUM_v1.md`. LB00 verified that v2 corrects only those statuses plus explicit revision metadata; it links v1 by the correct digest. All original records are preserved. The completed-input v1 receipt already said PROVED; the coordinator's fresh checks and this new registry independently confirm PROVED. This corrects bookkeeping, not theorem statements or evidence.

## Downstream checks

```text
python3 scripts/check_dependency_receipt.py LB01-v1
```

returned `LB01-v1 DEPENDENCIES_OK`. The previously registered LB06 dependency receipt also still passes. Because the original scripts are frozen, the separate additive checker should precede the usual private lane build whenever these imports are consumed. It checks original freezes, registered source hashes, dependency/compiler pins, supporting artifacts and exact new output fingerprints.

Rebuilds remain coordinator-only. For replay, check `LB01-v1 --sources-only`, run the serialized build above, then run the full receipt check. A mismatch requires investigation or a new explicit version; never rewrite the old manifest. No amendment to the frozen mathematical contract was required for this integration. Any lane with an original independence restriction must obtain explicit additive dependency authorization before adopting an unplanned Model import.
