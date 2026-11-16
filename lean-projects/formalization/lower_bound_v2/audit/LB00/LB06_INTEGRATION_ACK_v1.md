# LB-00 integration acknowledgement: completed LB-06 v1

Status: **INTEGRATED_COMPLETED_INPUT**. Recorded 2026-10-01T15:55:18.204116+00:00.

The coordinator rebuilt all thirteen released Types modules into `.build/lib/lean` and verified the exact theorem:

```lean
import RiffleLowerV2.Types.Main
-- RiffleLowerV2.Types.roundedType : RiffleLowerV2.Targets.RoundedTypeTarget
```

This completes the coordinator integration of manuscript `lem:type-estimates`. The final empirical and macroscopic lower-bound endpoints are not certified by this receipt.

## Evidence and immutable identities

- Lane receipt: `audit/LB06/COMPLETION_v1.md`, SHA-256 `d1a0cdd8ec24e1ef500ba066308f0d93d4c914db34075c711986d147dafdced2`.
- Lane manifest: `audit/LB06/SHA256_v1.json`, SHA-256 `2745e8a5970fa453430a75d45169d15496677db67524e137e5617655a09b5491`; every bound source and artifact matched before and after the build.
- New source/output registration: `Contracts/dependencies/LB06-completed-v1/SOURCES.json`.
- New additive manifest: `Contracts/dependencies/LB06-completed-v1/SHA256.json`, SHA-256 `73fabf05e9d20ab92bc5908e9c65e47902d53bf0996de67a2ea4758654e33b12`.
- Original v1 manifest SHA-256: `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`; all bound files and original external-source hashes remain unchanged.
- Compiler: Lean (version 4.33.1, arm64-apple-darwin24.6.0, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release); mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

The earlier `LB06-v1` registration remains the separate Analysis/Multinomial/Stirling dependency receipt. The new `LB06-completed-v1` registration certifies the actual lane result. No existing manifest was replaced or regenerated.

## Independent coordinator checks

The serialized command `python3 build.py RiffleLowerV2.Types.Main` returned `BUILD_OK` and newly compiled exactly the thirteen owned Types modules. No lane output was copied into the shared cache. The log is `audit/LB00/LB06_integration_build_v1.log`; the immutable build-provenance snapshot is `audit/LB00/LB06_integration_build_provenance_v1.json`.

The unchanged `audit/LB06/Check_v2.lean` then compiled with warnings treated as errors against only the coordinator overlay. It verified that roundedType is an actual theorem with the literal frozen target type. All 287 new declaration records match the lane's compiled audit exactly, including private/generated helpers, exact types and direct dependencies. The axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`. All 151 public-export records agree after excluding their additional source-location metadata. Records: `audit/LB00/LB06_integration_declarations_v1.json`; successful log: `audit/LB00/LB06_integration_audit_v1.log`.

The final counting/construction, truncation, mass-bin, word/rate and assembly reviews were inspected with their final source hashes. They resolve support/zero-coordinate handling, natural-division exactness, actual retained-law normalization, two-sided entropy error, global least-bin ties and uniform constants. The final assembly constructs `constructedTypeData` and supplies `constructedTypeData_spec`; generic helper premises are discharged by actual proved constructions. The first lane audit-script failure remains historical and is superseded by its separate successful v2 script; neither was overwritten.

The concrete theorem chooses typeConstant(k,C) before T,xi,m, and chooses roundConstant(k,m,T,log(1/xi)) and the universal threshold ceil(exp(1))+2 before P,cuts,I,alpha. The coefficient is `1+10C+40C exp(C)+99k^5`; the finite coefficient is `kmB+2+m(2k+1)(log(T+1)+3)+log(2+TB)`, with B=log(1/xi). Empty cells/selected sets and the full frozen cutoff range are retained. The spatial term stays a fixed budget at fixed xi; only the logarithmic rounding rate is proved vanishing. No LB05 theorem, time-profile approximation or macroscopic integrability hypothesis was added.

## Downstream and ledger

Before the usual owned-lane build, consumers should run:

```text
python3 scripts/check_dependency_receipt.py LB06-v1
python3 scripts/check_dependency_receipt.py LB06-completed-v1
```

Both passed. LB01-v1 and LB04-v1 also remain valid. The separate checks are necessary because the historical frozen lane tools do not automatically read later receipts. Consumers can now import `RiffleLowerV2.Types.Main`; exact additional public types, including constructedTypeData and its specification, are in `audit/LB06/EXPORTS_v1.md` and its machine-readable inventory.

`audit/LB00/INTEGRATION_LEDGER_v1.md` and `.json` provide a new additive status snapshot: LB01's eight frozen exports and LB06's one are proved and integrated, nine of 58. Other lanes have not received completed-input coordinator certification in this snapshot; this is not a claim about the absence of their ongoing work. Endpoints E and M remain uncertified. The original LEDGER.md, OWNERSHIP.json, shared umbrella, sources and all previous audits/releases stay unchanged. No downstream proof work was started.
