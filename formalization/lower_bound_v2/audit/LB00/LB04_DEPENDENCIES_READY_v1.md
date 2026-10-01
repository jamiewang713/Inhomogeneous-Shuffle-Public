# LB-00 additive dependency and reuse receipt LB04-v1

Status: **DEPENDENCIES_READY_AND_REUSE_AUTHORIZED**. Recorded 2026-10-01T15:48:16.654860+00:00.

LB04 may now consume the imports below in its owned proofs. Its ten mathematical target types remain exactly v1. The completed three-review comparison and unchanged interface are acknowledged separately in `audit/LB00/LB04_INTERFACE_ACK_v1.md`. No LB04 theorem is certified by this dependency receipt.

## Explicit dependency authorization

`Contracts/dependencies/LB04-v1/REUSE.md` is the versioned before/after comparison and authorization of the additional LB04-to-completed-LB01 helper dependency. The baseline prohibited unplanned dependencies on another first-stage lane; this reviewed addendum expressly permits `RiffleLowerV2.Model.GraphSorting` and `RiffleLowerV2.Model.FiniteLaws`. Their checked generic deterministic path-sort and elementary PMF lemmas may be reused directly. No source port is required. The dependency has no cycle and waits on no pending proof: LB01's completed input was rebuilt and audited by LB00 before this authorization.

LB04 retains ownership only of Ascent/ and audit/LB04/. It does not gain permission to edit Model, Shared, Contracts, compiler caches or historical records. The mathematical hypotheses and all ten required exports are unchanged. Other unplanned lane/module dependencies require a further explicit addendum.

## Registered imports and provenance

| Approved import | Source SHA-256 |
|---|---|
| `Mathlib.Probability.Moments.SubGaussian` | `7259bc145c6de9bb81b8aea24a660b951f12787ffdb7514ba27de74fb658e151` |
| `Mathlib.Probability.ProbabilityMassFunction.Integrals` | `174951d99036d6995b4ac6d486de807bedb58f340aa902f02502a7216515bf63` |
| `RiffleLowerV2.Model.GraphSorting` | `66201c1a8aa75da4d0fd5855ab251d3cded0e3fb90e5df734c6c95862be880f0` |
| `RiffleLowerV2.Model.FiniteLaws` | `cc5abe4ecf21f682658ca77e7a867368a4f1f8c4ab0b9d70eba79a9041772a06` |

`Mathlib.Probability.ProbabilityMassFunction.Integrals` was already registered and compiled in the v1 foundation. The coordinator built the missing pinned `MeasureTheory.Measure.Tilted`, `Probability.Moments.Tilted` and `Probability.Moments.SubGaussian` modules locally. All seven mathlib source records from this build were compared byte-for-byte with pinned Git HEAD. The approved Model modules were already compiled by the separate completed-LB01 integration and are unchanged.

- Original v1 manifest digest: `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`.
- New registry: `Contracts/dependencies/LB04-v1/SOURCES.json`.
- New manifest: `Contracts/dependencies/LB04-v1/SHA256.json`, digest `f4ace98aac793dda4a51f46011e817edcf82c9014271ae5d0f1cdff0df4449ac`.
- Required completed LB01 manifest digest: `3144d85b8d51329be36df3a86670509a3853cd67ada2371beef31e51fa7f58aa`.
- Compiler: Lean (version 4.33.1, arm64-apple-darwin24.6.0, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release); mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

The new manifest binds the dependency comparison, reviews/proposal/resolution, compiled declaration inventory, build/audit evidence and the completed LB01 supporting artifacts. No old manifest was regenerated. Every historical v1 bound file and external-source hash still passes.

## Checked declarations and remaining applications

`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` centers a bounded a.e.-measurable random variable by its integral and supplies parameter `(‖b-a‖₊/2)^2` under a probability measure. `HasSubgaussianMGF.mgf_le` applies to every real parameter t. Taking the indicator range [0,1] yields exponent t²/8 once LB04 proves the finite-measure/indicator application and translates through the checked `RiffleLowerV2.expect_eq_integral`. No added measurability or integrability hypothesis belongs in the frozen finite `BernoulliMGF` target: discharge the required conditions for the finite discrete model.

The Model path-sort helpers were checked on their exact types for arbitrary deterministic G; they assume no graph-law representation. Their probability helpers retain only their ordinary finite PMF/equivalence premises. Exact names, types, defining modules and axiom sets for all 301 examined declarations across the six checked modules are in `audit/LB00/LB04_dependency_declarations_v1.json`.

`audit/LB00/LB04DependencyCheck_v1.lean` imports these modules together with the frozen foundation, checks the requested APIs, and rejects any axiom outside `propext`, `Classical.choice`, `Quot.sound`. It passed with warnings treated as errors. This validates dependencies; the relative-order counting, parity argument, sharp concentration, clipped expectation and scan proofs remain LB04 obligations.

## Build evidence and downstream use

Coordinator command, successful with `BUILD_OK`:

```text
python3 build.py Mathlib.Probability.Moments.SubGaussian Mathlib.Probability.ProbabilityMassFunction.Integrals
```

Build log: `audit/LB00/LB04_dependencies_build_v1.log`.
Immutable build provenance: `audit/LB00/LB04_dependency_build_provenance_v1.json`.
Successful audit: `audit/LB00/LB04_dependency_check_v1.log`.

Before the unchanged private lane build, run:

```text
python3 scripts/check_dependency_receipt.py LB01-v1
python3 scripts/check_dependency_receipt.py LB04-v1
python3 scripts/lane.py LB04 RiffleLowerV2.Ascent.Main
```

Both additive checks passed. The older LB06 dependency check also still passes. These extra checks are explicit because frozen v1 lane tooling is unchanged and cannot automatically validate later receipts. The private builder links the registered coordinator outputs read-only; only LB04-owned source is compiled by its lane command. LB00 has not run LB04 proof sources.

For dependency replay, the coordinator may use `--sources-only` on the appropriate receipt before the serialized build, followed by the full output check. A fingerprint mismatch must be investigated or recorded in a new reviewed version; it must never be hidden by rewriting old hashes. All original sources, umbrellas, ownership records, audits and contracts are preserved.
