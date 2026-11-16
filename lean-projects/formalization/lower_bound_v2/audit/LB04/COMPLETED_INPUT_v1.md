# COMPLETED_INPUT — LB04 / v1

**LB04 is complete. All ten frozen targets are proved on the shared definitions, with no pending LB04 mathematical obligation.** The complete lane builds without warnings. The audit checks all 269 new elaborated declarations; the axiom union is exactly `Classical.choice`, `Quot.sound`, and `propext`.

## Downstream import and exact targets

```lean
import RiffleLowerV2.Ascent.Main
```

The declarations are under `RiffleLowerV2.Ascent`; the exact frozen types are under `RiffleLowerV2.Targets`.

| Theorem | Exact frozen type |
|---|---|
| `componentConcentration` | `ComponentConcentration` |
| `componentExpectation` | `ComponentExpectation` |
| `uniformScan` | `UniformScan` |
| `componentComparison` | `ComponentComparison` |
| `uniformGraphScan` | `UniformGraphScan` |
| `relativeOrderIndependence` | `RelativeOrderIndependence` |
| `boundaryAscentProbability` | `BoundaryAscentProbability` |
| `bernoulliMGF` | `BernoulliMGF` |
| `leastSuccessfulTranslate` | `LeastSuccessfulTranslate` |
| `componentConcentrationTwoSided` | `ComponentConcentrationTwoSided` |

[EXPORTS_v1.md](EXPORTS_v1.md) contains all 163 exact compiled public types. [DEPENDENCY_LEDGER_v1.md](DEPENDENCY_LEDGER_v1.md) maps every assigned source label and records the concrete discharge of intermediate premises. [COMPLETED_INPUT_v1.json](COMPLETED_INPUT_v1.json) binds the final source and audit hashes.

## Proved behavior and constants

Joint relative-order uniformity and independence are proved by an explicit finite block-action bijection and double counting; `relativeOrder_fiber_card_mul` exports the exact natural factorial count. The inverse-binomial boundary probability covers empty sets through the frozen quantified comparison event.

The actual component-sorted ascent statistic is decomposed into every retained internal graph edge plus boundary indicators. Exact joint relative-order factorization applies on disjoint component-pair supports within each component-index parity. Bernoulli MGFs and Cauchy–Schwarz give both weak one-sided bounds `exp(-t²/M)`, and the two-sided bound has coefficient 2. Zero retained boundaries are handled before division. There is no boundary-size premise in concentration.

Clipped expectation is exactly `e/2+r/6-d`, with d the full integer-path edge boundary. Internal edges in partial components are retained. Partial-component counting and separate left/right charging are proved, and the inverse-binomial probability is concretely supplied.

The uniform scan uses arbitrary deterministic integer H0 and precisely N+1 shifts, with bound `(N+1) exp(-s²/M)`. Conditional failure is the weak event and has exact bound `exp(-(r/6-d-s)²/M)` for positive gap. At the asymptotic threshold `s=M^(1/2+delta/2)`, the sufficient conditions `M>0`, `M^delta≥576`, `M^delta≥24D` give error `exp(-M^(2delta)/144)`. The eventual N0 precedes N,H0,G and depends only on a,delta,D,epsilon; no M≤N or support restriction is added.

`chosenTranslate` is a total graph-only least-successful-index function, with default zero and a checked discrete measurability theorem. It has no sampled permutation input.

`conditionalLalleyTest` strengthens the deterministic graph scan to a uniform TV test for any graph law rho and permutation law P satisfying the explicit identity `P=pathGraphMixture rho`: for every positive accuracy epsilon, one N0 works for every N,H0,rho,P and yields `probability rho graphSuccess-epsilon ≤ tv P uniform`. `conditionalLalleyTendsto` gives TV→1 when graph success tends to one and the geometry holds eventually. These are explicitly conditional intermediates. LB10 must discharge the actual shuffle mixture identity using LB01. No actual-shuffle law assumption is presented as proved by LB04, and the full lower-bound endpoints are not claimed.

## Verification and independent review

From the integration package:

```text
python3 scripts/check_dependency_receipt.py LB01-v1
python3 scripts/check_dependency_receipt.py LB04-v1
python3 audit/LB04/compile_lane.py RiffleLowerV2.Ascent.Main
# delegates to python3 scripts/lane.py LB04 RiffleLowerV2.Ascent.Main
python3 audit/LB04/check_compiled.py
```

Final build: [build-20261001T160330161378Z.log](build-20261001T160330161378Z.log), `LB04 BUILD_OK`, exit 0, no warnings. Complete exact-type and axiom audit: [compiled-audit-v1.log](compiled-audit-v1.log), `LB04_AUDIT_OK`, exit 0, warnings treated as errors. The 269-declaration inventory includes generated/private helpers and verifies all ten assignments to their exact frozen types. No custom axiom, placeholder, or native proof oracle enters the closure.

Three independent pre-proof reviews and their comparison were acknowledged by LB00 before proofs began. Independent final reviews passed for [relative orders](relative_order_final_review_v1.md), [clipped expectation](expectation_final_review_v1.md), [analytic machinery and asymptotics](analytic_final_review_v1.md), and [concrete concentration/scan/selection/conditional test](concentration_final_review_v1.md). All reviewed source hashes match the delivered sources; no substantive finding remains unresolved. Supplemental enumerations are diagnostic only and are not used as proof.

## Provenance and integration

The authoritative manuscript hash remains `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`; the frozen v1 manifest remains `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`. The compiler is Lean 4.33.1 and mathlib is pinned to `0df444a360eaa60ab8c11dca51a86af692955474`.

Approved extra imports are recorded in LB00's additive `LB04_DEPENDENCIES_READY_v1.md` and `Contracts/dependencies/LB04-v1/REUSE.md`. They authorize only the completed generic Model.GraphSorting/FiniteLaws helpers and registered pinned analytic inputs. [provenance_v1.md](provenance_v1.md) explains the limited legacy proof-pattern adaptation and the new concrete PMF proofs. No original package, manuscript, shared definition, contract, umbrella or old freeze was changed.

The coordinator may compile `RiffleLowerV2.Ascent.Main` into its integration overlay for downstream use. This requires no mathematical contract change. Existing development logs and historical records are preserved.
