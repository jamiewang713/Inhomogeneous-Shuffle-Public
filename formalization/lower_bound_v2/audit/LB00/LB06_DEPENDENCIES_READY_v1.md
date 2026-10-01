# LB-00 additive dependency receipt LB06-v1

Status: **DEPENDENCIES_READY**. Recorded 2026-10-01T15:29:45.886158+00:00.

This receipt supplements `audit/LB00/LB06_INTERFACE_ACK_v1.md`. The unchanged `RiffleLowerV2.Types.roundedType : RiffleLowerV2.Targets.RoundedTypeTarget` interface remains the required LB06 export. No part of that target is proved by dependency registration.

## Frozen identities and provenance

- Original v1 manifest SHA-256: `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`; all 43 bound files and every original external-source hash passed verification after the dependency build.
- New additive manifest: `Contracts/dependencies/LB06-v1/SHA256.json`, SHA-256 `93330a2ba9e4e51a7aa5cd4cb876fd6ce8ad8c4d324c71f800c9089b5e5edad3`.
- New source/output registration: `Contracts/dependencies/LB06-v1/SOURCES.json`.
- Compiler: Lean (version 4.33.1, arm64-apple-darwin24.6.0, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release).
- Compiler SHA-256: `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554`.
- Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`; all original dependency revisions remain pinned.

| Registered import | Source SHA-256 |
|---|---|
| `RiffleTimeProfile.Analysis` | `6cb844a02817905bc2e87f57277b23e68c2040dd2b1be6509d4b4320eeb3ac30` |
| `Mathlib.Data.Nat.Choose.Multinomial` | `7023cc66afa2ea732149a6847ee909d91b5df4fc04ed229aa03d24b664cbd8bb` |
| `Mathlib.Analysis.SpecialFunctions.Stirling` | `46849279daaa7b5a2800f4c3428b2c28066a235f1cb6623702312aa56ba50aac` |

The canonical Analysis source was rebuilt verbatim into the package-local `.build/lib/lean` using the pinned compiler. No old time-profile output, vendor tree, compatibility port, manuscript edit, or canonical source edit was used. The two mathlib sources and all other recorded pinned-library sources match their pinned Git revision byte-for-byte. Nine missing modules were built locally, with 36 source records in the build traversal. Existing cached transitive mathlib imports retain the original pinned-library policy; this record does not claim a fresh rebuild of all mathlib.

The immutable build snapshot is `audit/LB00/LB06_dependency_build_provenance_v1.json`; the successful build log is `audit/LB00/LB06_dependencies_build_v1.log`. The additive manifest binds both along with the new checker and audit artifacts. All new output fingerprints are registered separately from historical freezes.

## Verified interfaces and axiom closure

The exact regular-partition theorem was checked under the compatible imports:

```lean
TimeProfile.exists_regular_partition {k : ℕ} (_hk : 2 ≤ k) {chi : ℝ}
    (hchi : 0 < chi) (_hchiK : chi < 1 / (k : ℝ)) :
    ∃ P : TimeProfile.BorelPartition k, P.IsRegular chi 1
```

Its constant is 1, independent of chi. This existential theorem does not replace the arbitrary partition in RoundedTypeTarget or license replacement of a macroscopic hypothesis's selected partition. Any construction using it must discharge its stated premises.

Also checked: `Nat.multinomial`, `Nat.multinomial_spec`, `Stirling.log_stirlingSeq_formula`, `Stirling.log_stirlingSeq'_antitone`, and `Stirling.log_stirlingSeq_bounded_by_constant`. The multinomial specification states the exact natural factorial-product identity. The Stirling declarations provide finite logarithmic ingredients; the required two-sided rounded-type error, natural-to-real quotient identities, zero cases and uniform constants still belong to LB06.

`audit/LB00/LB06DependencyCheck_v2.lean` jointly imports the frozen shared package and all three requested modules. It inspected all 364 imported environment declarations belonging to the nine newly compiled modules and checked their transitive axiom closure: only `propext`, `Classical.choice`, and `Quot.sound`. It succeeded with warnings treated as errors. Exact names, types, defining modules and axiom sets are recorded in `audit/LB00/LB06_dependency_declarations_v1.json`; the corresponding log is `audit/LB00/LB06_dependency_check_v2.log`.

The first audit-script attempt lacked a Nat annotation on its counter and failed elaboration; its source/log are preserved as v1. The corrected separate v2 audit passed. This was an audit-script inference error, not a dependency theorem failure; the source dependency build passed on its first attempt.

## Downstream use and replay

From the package root, run the additive read-only check before the unchanged private lane command:

```text
python3 scripts/check_dependency_receipt.py LB06-v1
python3 scripts/lane.py LB06 --check-ready
python3 scripts/lane.py LB06 RiffleLowerV2.Types.Main
```

The first two returned `LB06-v1 DEPENDENCIES_OK` and `LB06 CONTRACT_INPUTS_OK`. The third is the lane's own subsequent proof build; LB00 has not run or certified LB06 proof files. The three registered imports are available from the coordinator overlay and will be linked read-only by the existing private lane builder. No umbrella import or target was changed.

Because the v1 build/lane scripts are immutable, their original readiness check does not automatically verify this new receipt. The separate checker explicitly verifies both historical v1 and these additive source/compiler/dependency/output identities. It is read-only and never creates dependencies.

For a coordinator-only dependency replay, first use `python3 scripts/check_dependency_receipt.py LB06-v1 --sources-only`, then the existing serialized command:

```text
python3 build.py RiffleTimeProfile.Analysis Mathlib.Data.Nat.Choose.Multinomial Mathlib.Analysis.SpecialFunctions.Stirling
```

Then rerun the full additive check. Missing outputs may be rebuilt from their registered sources in the package-local cache; never overwrite the receipt or regenerate old hashes to accommodate a mismatch. Any genuine source/interface change requires a new reviewed additive version. The successful audit can be replayed with the pinned compiler, `LEAN_PATH` set only to this package's `.build/lib/lean`, `-R` set to the package root, and `-DwarningAsError=true audit/LB00/LB06DependencyCheck_v2.lean`.

LB06's three reviews and comparison are complete and acknowledged in the earlier receipt. Proof work can proceed within its owned paths under the unchanged contract. All historical releases, audits, canonical sources and lane-owned files were preserved.
