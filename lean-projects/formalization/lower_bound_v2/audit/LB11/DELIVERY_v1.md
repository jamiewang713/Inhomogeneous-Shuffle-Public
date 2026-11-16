# LB11: scalar-integrable macroscopic lower bound

The uniform macroscopic endpoint is proved for the actual chronological physical inverse-shuffle law, with the explicit same-partition scalar-integrability assumption. Its exact frozen type is unchanged. A sequence-convergence corollary is derived from that uniform theorem. There are no pending LB11 mathematical obligations.

This is **not an unchanged-assumption theorem for arbitrary totalized TimeLaw**. The empirical endpoint has no temporal regularity premise; the macroscopic endpoint below has the visible additional scalar predicate. Original packages, historical statements, frozen contracts and the manuscript remain unchanged.

## Exact exports and source correspondence

Import `RiffleLowerV2.MacroscopicLower.Main`.

```lean
RiffleLowerV2.MacroscopicLower.macroscopicIntegrable :
  RiffleLowerV2.Targets.MacroscopicIntegrableTarget
```

This is a theorem declaration whose elaborated type is literally the frozen constant. The audit checks both facts, rather than accepting a proposition-valued target definition as evidence.

`RiffleLowerV2.MacroscopicLower.macroscopicIntegrable_tendsto` is the convenience sequence corollary: for the same ordered partition and parameter choices, a fixed scalar-integrable profile and any sequence of cuts that eventually satisfies AlmostLike and LocalGood, the physical inverse law's TV distance from uniform tends to one whenever the macroscopic maximum margin is at least eta. Its proof calls the uniform theorem and `Ascent.tv_le_one`.

`EXPORTS_v1.md` gives all eight exact public declaration types, the complete compiled expansion of the uniform target, and the complete scalar predicate. `compiled-declarations-v2.json` retains all 17 owned declarations, including generated proof helpers, their direct type/value dependencies, and their transitive axiom closures.

| Source label | Checked declaration and role |
|---|---|
| `thm:buffered-reduced-lower-bound` | `MacroscopicLower.macroscopicIntegrable`, exact uniform endpoint with explicit scalar regularity |
| Same theorem, sequence formulation | `MacroscopicLower.macroscopicIntegrable_tendsto`, derived corollary |
| `lem:lower-profile-transfer` | `ProfileTransfer.profileTransfer`, imported actual two-sided transfer |
| `prop:cold-lower` | `EmpiricalLower.coldOnly`, imported actual finite cold endpoint |
| `prop:largest-prefix` | `EmpiricalLower.largestOnly`, imported actual largest-word endpoint |

## Exact uniformity and additional assumptions

Fix k>=2, T>0 and eta>0. There exist chiPartition>0, chiPartition<1/k, a regular partition P and rho0>0 with

```text
2*rho0*log k <= kappa0(eta/2)/100.
```

For every fixed rho in (0,rho0], there is phi0>0. For every fixed phi in (0,phi0], positive chiGood and gamma, accuracy epsilon>0, and profile mu satisfying ScalarIntegrable(mu,P,T), there exists N0>=2 such that **every N>=N0 and every cut array** of depth floor(T log N) satisfying

```text
AlmostLike(cuts,mu,P,T,rho,phi),
LocalGood(cuts,chiGood,gamma,rho,0,T),
eta <= max(macroBeta(mu,T),macroLambda1(mu,T))
```

has TV(physicalInverseLaw(cuts),uniformPermutation(N))>=1-epsilon.

The fixed profile and all local parameters precede N0; N and cuts follow it. P is chosen from k,T,eta before the scalar-integrability premise, is independent of N, and is never replaced or refined. The final N0 is the maximum of the transfer, logarithmic-tail, largest-word and cold-endpoint thresholds. It works regardless of which branch occurs for each N or each array.

The additional scalar predicate is exactly

```lean
(∀ i, IntervalIntegrable (cellMass μ P i) volume 0 T) ∧
IntervalIntegrable (profileMaxCost μ) volume 0 T ∧
∀ α ∈ Icc (2 : ℝ) 4,
  IntervalIntegrable (fun t => profilePsi μ t α) volume 0 T
```

There is no measurable-probability-kernel hypothesis, time continuity, differentiability, macro J/H integrability, global positive lower bound on every pile, upper first-moment input, homogeneous substitution, random-pile extension, or zero-margin conclusion. LocalGood remains the original local condition on actual columns.

The current manuscript's lines 148–152 require ordinary integrability of all displayed scalar time integrands, explicitly including cell probabilities. The predicate above uses only the subset needed for this proof. Relative to the historical unrestricted `TimeLaw := ℝ → ProbabilityMeasure (Simplex k)`, it is a genuine strengthening. Fixed-partition AlmostLike alone does not imply it: same-cell nonmeasurable switching leaves cell masses unchanged while cost profiles may be nonintegrable. That example refutes the unregularized two-sided-transfer step; this delivery does not claim it independently disproves every possible historical endpoint theorem.

## Parameter and branch verification

The implementation fixes eta_f=eta/2, kappa=eta_f/1000 and kappa0=min(kappa/100,1/1000). It chooses

```text
e = min(kappa0/10,eta/100)/2,
rhoCeiling = (kappa0/100)/(2 log k).
```

The standalone checked lemmas prove 0<e<min(kappa0/10,eta/100), positivity of rhoCeiling, the exact cold bridge restriction, and kappa0<=eta/200000. Applying LB07 with this ceiling selects P before any profile-integrability requirement.

`ProfileTransfer.transferThreshold_spec (log k)` at tolerance e makes d_N=log k/log N<=e/4. The frozen transfer errors are consequently at most 5e/4 for beta and 10e for lambda1. No terminal error or clipping term is dropped.

If empirical beta>=kappa0, the proof calls the actual `largestOnly` theorem. Otherwise `small_beta_forces_cold` uses both lower sides of the absolute-error bounds to show macroBeta<eta; the maximum-margin premise forces macroLambda1>=eta, and then empirical lambda1>=eta/2. It calls the actual `coldOnly` theorem with the constructed ColdParameters and the supplied LocalGood hypothesis. All generic arithmetic inputs are discharged for the actual margins; no witness, test-success, localization, graph-law or TV conclusion is assumed.

## Proved-versus-pending dependency ledger

| Obligation | Evidence | Status |
|---|---|---|
| Unchanged shared model and target | Frozen v1 manifest and LB00 receipts | Verified |
| Selected-P two-sided scalar transfer | LB07-v1, `ProfileTransfer.profileTransfer` | Discharged |
| Actual physical largest-word endpoint | LB10-v1, `EmpiricalLower.largestOnly` | Discharged |
| Actual physical cold endpoint, including all finite probabilistic inputs | LB10-v1, `EmpiricalLower.coldOnly` | Discharged |
| Positive choices, exact bridge bound and branch arithmetic | `Parameters.lean` | Proved |
| Exact uniform macro endpoint and alternating cases | `Main.lean`, `macroscopicIntegrable` | Proved |
| Sequence limit | `macroscopicIntegrable_tendsto` and checked TV<=1 | Proved |
| Independent final source/type/hypothesis/closure review | Three final reports and recursive closure evidence | Passed |
| LB11 mathematical obligations | Complete checked proof closure | None pending |
| Coordinator registration of completed LB11 and later LB12 certification | Outside this lane's exclusive files | Separate downstream integration/audit |

The upstream inputs were freshly rebuilt and registered by LB00 as `LB07-v1` and `LB10-v1`. The exact unchanged interface is acknowledged in `audit/LB00/LB11_INTERFACE_ACK_v1.md`; joint import readiness is `audit/LB00/LB11_DEPENDENCIES_READY_v1.md`. All of these are hash-bound in final verification v2. No sibling lane cache was copied or mixed.

## Build, axiom closure and independent review

Successful complete verification, from `formalization/lower_bound_v2`:

```text
python3 audit/LB11/verify_lane_v2.py v2
LB11 BUILD_OK
LB11 VERIFIED: 17 declarations
```

The underlying lane build is

```text
python3 scripts/lane.py LB11 RiffleLowerV2.MacroscopicLower.Main
```

Evidence: `final-build-v2.log`, `final-audit-v2.log`, `dependency-checks-v2.log`, and `VERIFICATION_v2.json`. The complete source build has no warnings or errors; the declaration audit treats warnings as errors. Reproduction must use a fresh evidence suffix, for example `python3 audit/LB11/verify_lane_v2.py v3`; scripts refuse to overwrite previous logs.

Runtime: Lean 4.33.1, compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6; mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. All 17 owned declarations have transitive axiom closure contained in exactly `propext`, `Classical.choice`, `Quot.sound`. No sorry, admit, custom axiom, unproved placeholder or native proof oracle is used.

The independent representation reviewer also recursively traversed opaque theorem bodies and all reachable type/value constants: 50,441 declarations for the uniform theorem and 50,443 for the corollary. Both recursive axiom sets match Lean's collectAxioms result and contain only the three standard axioms. The full graph evidence is `representation_closure_v1.json`; its size reflects complete dependency traversal rather than additional hypotheses.

Pre-proof reports are `math_review_v1.md`, `representation_review_v1.md`, and `hypotheses_review_v1.md`; their comparison is `REVIEW_RESOLUTION_v1.md`. Final reports are `final_math_review_v1.md`, `final_representation_review_v1.md`, and `final_hypotheses_review_v1.md`, with a separate independently compiled parameter review. All final proof-source hashes agree. No mathematical or representation revision remains requested.

`PROVENANCE_v1.json` records exact imports, source hashes, source-label correspondence and coordinator acknowledgements. `COMPLETION_RECEIPT_v1.json` supplies the hash-bound handoff for LB00/LB12. Only owned proof/audit files and the assigned LB11 build overlay were written by this lane. The manuscript retains SHA-256 672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d, and the original v1 contract retains its released hash.
