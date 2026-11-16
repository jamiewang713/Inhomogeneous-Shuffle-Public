# LB09 completed proof delivery v1

**LB09_PROVED.** All five required declarations are proved theorems of their exact unchanged frozen types. The actual deterministic cold sets and full-word families are constructed; their quantitative geometry is proved; one event localizes every tail and supplies an injective repeated-word-to-internal-edge map. No geometry, reserve event or localization assumption remains in the final empirical theorem. No LB09 proof obligation is pending.

## Downstream entry point and exact exports

```lean
import RiffleLowerV2.Localization.Main

RiffleLowerV2.Localization.relativeEndpoint :
  RiffleLowerV2.Targets.RelativeEndpointTarget
RiffleLowerV2.Localization.deterministicColdGeometry :
  RiffleLowerV2.Targets.DeterministicColdGeometryTarget
RiffleLowerV2.Localization.localization :
  RiffleLowerV2.Targets.LocalizationTarget
RiffleLowerV2.Localization.coldGeometryFromEmpirical :
  RiffleLowerV2.Targets.ColdGeometryFromEmpiricalTarget
RiffleLowerV2.Localization.lB09 :
  RiffleLowerV2.Targets.LB09Target
```

These types are verified from the compiled environment as theorem constants, not merely propositions naming desired results. Complete exact helper types, source positions and transitive axioms are in `EXPORTS_v1.md` and `public-exports-v1.json`; `compiled-declarations-v1.json` also records private/generated declarations and direct type/value dependencies.

## Authoritative source correspondence

Manuscript: `time_inhomogeneous_riffle_shuffle_unified_article.tex`, SHA-256 `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`, unchanged from the planning snapshot.

| Manuscript source | Final theorem/modules | Implemented conclusion |
|---|---|---|
| `lem:cold-geometry`, line 3357 | `deterministicColdGeometry`; Words, Bridge, Intervals, ProbabilityIntervals, ColdSet, Geometry and Geometry/* | Actual ambient prefix, rounded prefix/tail classes, bridge/reserves, relative integer union and full family; exact mass/cardinality, exponent, boundary and digit-floor bounds |
| `lem:finite-relative-endpoints`, line 3518 | `relativeEndpoint`; WordOrder, Endpoints and Endpoints/* | Exact first-difference identities and the stated finite endpoint error; right ambient fluctuation retained; all finite degenerate cases included |
| `lem:localization`, line 3575 | `localization`; Concentration, EventBounds, RankBarriers, Edges, Probability, Events | One-event localization for every tail and every occurrence, actual probability estimate and injective internal-edge assignment |
| Empirical composition of these lemmas with LB05/LB06 | `coldGeometryFromEmpirical`, `lB09` in Main | Concrete existential output and full frozen LB09 contract |

## Constants, event and uniformity

The deterministic geometry retains the frozen constants: exp(-2)N^h≤M≤2N^h, N^(kappa/3)≤M≤N, boundary≤4sqrt M, g−h/2≥kappa/2, z≤2kappa0, and exp(-2)N^z<mean(y)≤N^z. It preserves the bridge budget `2*rho*log k ≤ kappa0 eta/100`, fixed chiGood² factors and common digit floor `min xi (min chiGood (1/k))`.

The same actual `allPrefixEvent (kappa eta/4)` controls endpoints and every reserve prefix. Explicit scalar thresholds ensure

```text
4*k*T*log N + 4 ≤ N^(kappa/4),
4 ≤ N^(kappa/2),
16 ≤ N^(5*kappa/2).
```

Together with b≥4kappa and K≤T log N, they give endpoint error≤N^(b/2+kappa/2) and both reserve counts≥endpoint error+2. The rank proof applies to every tail z on this one sample/event and uses no tail-independence hypothesis.

`coldLocalization_failure_le_prefixFailure` bounds actual failure probability by `2*(K+1)*k^K*exp(-N^(kappa/4)/8)`. The directly exported `coldLocalization_failure_le_envelope` gives

```text
P(not ColdLocalization) ≤
  2*(T+1)*N^(1+T*log k)*exp(-N^(kappa/4)/8).
```

All scalar thresholds and the bound are uniform in later cuts, witnesses, geometry and words. Geometry selects xi and its regular partition P before N0; the empirical theorem selects xi and P before epsilon. The final probability threshold precedes cuts/W/G. The exact frozen target types make these orders explicit, and the independent final reviews check them.

## Build and axiom audit

From `/Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/lower_bound_v2`:

```sh
python3 audit/LB09/serial_build.py RiffleLowerV2.Localization.Main
```

This wrapper only serializes owned work before invoking the unchanged `python3 scripts/lane.py LB09 RiffleLowerV2.Localization.Main`. It compiled the complete owned Main import graph in the assigned `.build/lanes/LB09/lib/lean` overlay. Final log: `audit/LB09/main_build_v3.log`, ending `LB09 BUILD_OK`, with no warnings. Pinned runtime: Lean 4.33.1; mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The final read-only compiled-environment check was:

```sh
LEAN_PATH='.build/lanes/LB09/lib/lean' \
  '/Users/jialushi/Documents/loop soup/formalization/.tools/lean-4.33.1-darwin_aarch64/bin/lean' \
  -DwarningAsError=true audit/LB09/Check_v1.lean
```

Final log: `audit/LB09/compiled-audit-v2.log`. It succeeded and emitted `LB09_REQUIRED_THEOREMS_VERIFIED`. Every checked declaration has transitive axiom closure contained in `propext`, `Classical.choice`, `Quot.sound`; each required export has exactly those standard axioms. There is no admitted proof, custom axiom, native proof oracle or unproved generic input. The source scan, exact export inventory and source hashes were generated by `audit/LB09/export_inventory_v1.py`; see `verification-v1.json` and `export-inventory-v1.log`. Counts are inventory only, not the completion criterion.

`completion-input-check-v1.log` verifies all prerequisite receipts again, unchanged manuscript and frozen-contract hashes, and that every owned Lean source has compiled output newer than its final edit. Unsuccessful development logs and all prior audit versions are preserved.

## Reviews, provenance and dependency release

The required three independent pre-proof reviews and interface comparison were acknowledged by LB00 before dependent proofs. Final independent reviews of all implementation groups pass with no unresolved finding. See `REVIEW_RESOLUTIONS_v1.md`, the five linked component reports, and the completed dependency/obligation ledger `OBLIGATIONS_v2.md`.

Approved completed inputs are LB00, LB02 Thinning.Main, LB05 Witness.Main, LB06 Types.Main, plus the explicitly authorized optional LB01 Model.Sorting module. Dependency authorization and acknowledgement: `Contracts/dependencies/LB09-v1/REUSE.md`, `audit/LB00/LB09_INTERFACE_ACK_v1.md`, `audit/LB00/LB09_DEPENDENCIES_READY_v1.md`. `LB09-v1`, `LB02-v1`, `LB05-v1` and `LB06-completed-v1` receipt checks all pass. Full direct imports are in `IMPORTS_v1.json`.

Historical Matrices/Cold/Sorting sources were inspected read-only. The repeated-word edge argument is adapted at source level to the concrete v2 representation; actual localization is proved before its conditional finite helper is applied. `PROVENANCE_v1.json` records original/adapted hashes and correspondence. No historical binary cache is imported.

To consume this delivery, LB00 should independently rebuild `RiffleLowerV2.Localization.Main`, check `Check_v1.lean`, bind `SOURCES_v1.json` and the review records in an additive completed-output receipt, then register the module for downstream lanes. LB09 does not modify shared registrations, umbrella imports, configurations, contracts, other lanes, historical audits or the manuscript. This receipt certifies the completed LB09 implementation; coordinator integration is recorded separately by LB00.
