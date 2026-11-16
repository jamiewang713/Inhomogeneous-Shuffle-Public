# LB12 independent final lower-bound audit

## Separate verdicts

**Empirical endpoint E: PASS.** `RiffleLowerV2.EmpiricalLower.empiricalCombined : RiffleLowerV2.Targets.EmpiricalCombinedTarget` is a checked theorem of the unchanged frozen target. The concrete physical inverse-shuffle model, all intermediate proof obligations, and cut-uniform thresholds are discharged. E has no `TimeLaw` or scalar-integrability assumption, including in its elaborated dependency closure.

**Integrable-profile endpoint M: PASS with the explicit frozen scalar-integrability premise.** `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable : RiffleLowerV2.Targets.MacroscopicIntegrableTarget` is checked with `ScalarIntegrable μ P T` for exactly the selected partition P. Its sequence corollary is also checked. There is no unresolved adapter or assumed stochastic conclusion in either requested endpoint.

**Original unchanged arbitrary-TimeLaw statement: NOT CERTIFIED.** It is not the theorem proved by M. More strongly, deleting `ScalarIntegrable` from the present M is mathematically false under Lean's totalized-integral semantics; the counterexample below was independently checked by all three reviewers. This counterexample has not itself been formalized in Lean. It does not refute the revised manuscript, whose lines 148–152 expressly require ordinary measurable/integrable scalar time integrands.

No unresolved mathematical or verification obligation remains for E or scalar-integrable M. Removing the regularity premise would require a different, explicitly reviewed statement; the direct deletion is impossible.

## Scope, sources and frozen comparison

The task is the supplied LB12 prompt. All LB12 writes are under `audit/LB12/`. Substantive proof modules and the manuscript were not edited. The coordinator made only additive integration/verification changes in its own scope. Historical failed audit probes remain preserved and are not counted as certified results.

The manuscript SHA-256 is `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`. The immutable v1 contract manifest hash is `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`. All 43 frozen files, released external-source fingerprints, all snapshotted existing package proof sources, and 17,348 historical-file fingerprints were unchanged across the audit. This is comparison to the task-start snapshot; pre-existing user changes were retained.

The old `lean-lower-bound/FREEZE.md` explicitly excluded the asymptotic cold theorem and froze finite Chebyshev/run results only. The new theorem does not treat old localization or analytic gaps as assumptions. M's regularity addition was explicit in the initial new contract, not introduced while implementing a proof. E remains free of that addition. No target or premise was changed by LB12.

| Source label | Concrete checked declaration | Exact frozen type |
|---|---|---|
| `prop:largest-prefix` | `RiffleLowerV2.EmpiricalLower.largestOnly` | `RiffleLowerV2.Targets.LargestOnlyTarget` |
| `prop:cold-lower` | `RiffleLowerV2.EmpiricalLower.coldOnly` | `RiffleLowerV2.Targets.ColdOnlyTarget` |
| Empirical two-alternative assembly | `RiffleLowerV2.EmpiricalLower.empiricalCombined` | `RiffleLowerV2.Targets.EmpiricalCombinedTarget` |
| `thm:buffered-reduced-lower-bound`, with the explicit ordinary-integral convention | `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable` | `RiffleLowerV2.Targets.MacroscopicIntegrableTarget` |

[EXPORTS_v5.md](EXPORTS_v5.md) gives all 58 exact names, types, expanded target bodies, owner modules and source-label correspondences from the final compiled environment. The [elaborated inventory](compiled_declarations_v5.json) records every audited project declaration, its type, direct type/value/metadata dependencies, and recursive axioms. It is not described as a printout of every proof body; the accepted audit log explicitly prints the endpoint proofs, target expansions, important data structures and specification predicates.

## Hypotheses, parameter order and model

E fixes k≥2, T>0, positive empirical margins, the cold parameters and epsilon>0 before N0. Then it quantifies over every N≥N0 and every deterministic cut array. Cold-parameter positivity, the mesh budget and LocalGood occur only in the cold alternative. Its largest-word alternative has no local-good or macro-profile premise. Branch thresholds are maximized before cuts are introduced, so arbitrary alternation of branches and witnesses is covered.

M has the order `k,T,eta → chiPartition,P → rho0 → fixed rho → phi0 → fixed phi,chiGood,gamma,epsilon,μ with ScalarIntegrable μ P T → N0 → every N and cuts`. It promises no uniformity over profiles or fixed parameters allowed to change with N. The scalar assumption means interval integrability of P's cell masses, `profileMaxCost μ`, and every `profilePsi μ · α` for α∈[2,4]. It is neither a transfer estimate nor a TV conclusion.

`TimeProfile.Cuts`, `ShuffleSample` and `fixedCountPMF` are the actual fixed-count independent-column model. Stable sorting maps sorted positions to original labels. The physical chronological inverse and matrix law are independently defined and identified by the proved triangular sample bijection. The manuscript itself uses the chronological inverse law. An additional newly checked audit example verifies forward/inverse TV equality through `Model.inversionTV`.

Graph representation is a proved law identity. Its mixture draws a uniform permutation independently of the graph. The translate used for the observable scan is selected from the graph alone; the ambient-prefix shift proves existence, then the graph-only selector is used for testing. One-based manuscript rank is `i.val+1`, and `(L,U]` is identified with zero-based `[L,U)`. Finite-law compatibility ports are connected to canonical PMFs by checked constant-fibre/expectation identities; no old-version project object cache is imported.

The [hypotheses review](hypotheses_review_v1.md) gives a discharge table for every potentially hidden conclusion, including witness/geometry specifications, reserves, occupancy moments, prefix concentration, localization, many edges, law equality and scan success. The actual cold endpoint constructs these objects before applying its conditional helper lemmas.

## Mathematical and dependency review

[Mathematical review](math_review_v1.md), [representation review](representation_review_v1.md), and [hypotheses review](hypotheses_review_v1.md) are independent reports. The mathematical ledger covers all-positive-s thinning and residual conditioning; even Bonferroni expected remainders and the 1/3 coefficient; rare/mixed relative errors; theta=4 backward motion and terminal clearance; exact lower multinomial counts and fixed-xi errors; the ambient right-endpoint fluctuation; clipped-component deficit; graph-only selection; and two-branch asymptotics. No substantive E/M proof repair was required.

The final recursive walk uses the private compiled environment and `ConstantInfo.getUsedConstantsAsSet`: types, opaque proof values, inductive constructors, and recursor metadata. It rejects a nonstandard axiom at any depth and compares the result with `Lean.collectAxioms`. Every project declaration receives the axiom check, including generated/private declarations and canonical dependency modules. All 58 required exports are asserted to be theorems of their literal target constants, with no extra generalized binder, and are located in the assigned owner's proof module.

| Endpoint root | Reachable declarations, including trusted foundations | Axiom closure |
|---|---:|---|
| `RiffleLowerV2.EmpiricalLower.empiricalCombined` | 50,256 | `propext`, `Classical.choice`, `Quot.sound` |
| `RiffleLowerV2.EmpiricalLower.coldOnly` | 50,177 | `propext`, `Classical.choice`, `Quot.sound` |
| `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable` | 50,447 | `propext`, `Classical.choice`, `Quot.sound` |
| `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable_tendsto` | 50,449 | `propext`, `Classical.choice`, `Quot.sound` |

No custom axiom, `sorryAx`, unproved placeholder, or native-oracle dependency occurs in the accepted closure. `ScalarIntegrable` occurs in M's closure and is absent from E/cold's closure. All 364 frozen foundation declaration kinds, types and direct type/value dependencies match the original compiled inventory.

| Lane | Frozen exports | Downstream proof import | Status |
|---|---:|---|---|
| LB01 | 8 | `RiffleLowerV2.Model.Main` | Proved; exact types, owner modules and standard-only axiom closures checked |
| LB02 | 7 | `RiffleLowerV2.Thinning.Main` | Proved; exact types, owner modules and standard-only axiom closures checked |
| LB03 | 10 | `RiffleLowerV2.Factorial.Main` | Proved; exact types, owner modules and standard-only axiom closures checked |
| LB04 | 10 | `RiffleLowerV2.Ascent.Main` | Proved; exact types, owner modules and standard-only axiom closures checked |
| LB05 | 4 | `RiffleLowerV2.Witness.Main` | Proved; exact types, owner modules and standard-only axiom closures checked |
| LB06 | 1 | `RiffleLowerV2.Types.Main` | Proved; exact types, owner modules and standard-only axiom closures checked |
| LB07 | 4 | `RiffleLowerV2.ProfileTransfer.Main` | Proved; exact types, owner modules and standard-only axiom closures checked |
| LB08 | 3 | `RiffleLowerV2.Occupancy.Main` | Proved; exact types, owner modules and standard-only axiom closures checked |
| LB09 | 5 | `RiffleLowerV2.Localization.Main` | Proved; exact types, owner modules and standard-only axiom closures checked |
| LB10 | 5 | `RiffleLowerV2.EmpiricalLower.Main` | Proved; exact types, owner modules and standard-only axiom closures checked |
| LB11 | 1 | `RiffleLowerV2.MacroscopicLower.Main` | Proved; exact types, owner modules and standard-only axiom closures checked |

The [dependency graph](module_graph_v5.json), [endpoint closures](endpoint_closures_v5.json), and [export ledger](export_ledger_v5.json) are reproducible machine-readable evidence. The endpoint closures include every reachable name; direct project graph edges are in the declaration inventory. Counts measure coverage, not mathematical completeness.

## Fresh build and independent reproduction

Pinned runtime: `Lean (version 4.33.1, arm64-apple-darwin24.6.0, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)`. Compiler SHA-256: `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554`. Mathlib commit: `0df444a360eaa60ab8c11dca51a86af692955474`. The source and object manifests record every imported dependency fingerprint.

The coordinator built into an initially absent directory, `/Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/lower_bound_v2/.build/full_package_v1/lib/lean`, using the frozen builder with an isolated output override and the complete discovered module list. All 183 package source modules were freshly compiled; 197 total source modules were rebuilt, including required canonical dependencies and missing pinned-library overlays. Existing project/lane outputs were not reused. Pinned third-party caches were read-only. There were 14 benign style/linter warnings in the source build and no build errors; the accepted audits passed warning-as-error with no diagnostics.

The accepted coordinator audit is `audit/LB00/final_audit_v3`; its bound fresh-build evidence is `audit/LB00/full_package_v1`. Exact original commands and logs are in those directories' `COMMANDS.json`, `build.log`, `audit.log`, and `VERIFICATION.json`. The coordinator manifest SHA-256 is `868796a3bb25bb4b0411bee402f09559310b4fb0064cc61f5e84b6df4ca3b275`.

The final independent command, run from the package root, was:

```text
python3 audit/LB12/verify_final_v4.py v5 audit/LB00/final_audit_v3
```

Its accepted log is [independent_check_v5.log](independent_check_v5.log), ending with `PROCESS_EXIT 0`; the independent receipt is [VERIFICATION_v5.json](VERIFICATION_v5.json). It audits 3,216 project declarations and 5,417 imported modules, compares 15,867 object fingerprints including their actual resolved lookup paths before and after execution, and checks 3,885 imported-source fingerprints and dependency revisions.

For a later full reproduction, choose an unused version label and run `python3 scripts/verify_completed_v2.py --run vNEW`, followed by the same independent verifier with a fresh numeric audit version and the resulting `audit/LB00/final_audit_vNEW` path. Whole-package reproduction remains coordinator-owned; do not reuse an existing evidence label. The scripts validate numeric labels, so replace `vNEW` with an unused label such as `v20`.

## Integration, findings and resolutions

1. **M registration and umbrella, owner LB00:** at audit start ledger v9 registered 57/58 exports and the foundation umbrella imported only definitions. LB00 issued `INTEGRATION_LEDGER_v10` and the LB11 integration receipt, then the final `INTEGRATION_LEDGER_v11` and `Contracts/dependencies/COMPLETED-v1` receipt. Because the old umbrella is frozen, LB00 added `RiffleLowerV2.Completed`, importing all eleven proof entry points, and recorded `COMPLETED_UMBRELLA_COMPARISON_v1.md`. A separate independent environment imports only Completed and exact-checks all 58 exports; see [umbrella_check_v5.log](umbrella_check_v5.log). All production proof modules are reachable; the duplicate Contracts wrapper and diagnostic Check modules are separately covered by the all-module build.
2. **Manual dependency-graph coverage, owner LB12:** preliminary v2 followed only expression types/values. Independent instrumentation review required inductive/recursor metadata edges. The corrected v3 probe and final v5 checker include them and agree with `collectAxioms`. The final checker also verifies owner modules, actual imported-module coverage and object lookup paths, and places success after all commands.
3. **Coordinator generated-checker failures, owner LB00:** the first checker had a global placeholder replacement corrupting a diagnostic string; the next used Lean's reserved `prefix` keyword as a variable. These are retained failed instrumentation attempts, not project proof failures. The final versioned checker uses the same successful fresh build and passed. Historical evidence and freezes were not overwritten.
4. **Failed LB12 exploratory probes:** `IndependentCheck_v1` and `RepresentationCheck_v1` failed during development and emitted compiler recovery diagnostics. They produced no accepted object or theorem and are excluded from certification. Subsequent successful versions and the final independent audit supersede them explicitly. Textual `sorryAx` in an error log is not treated as a checked declaration; actual accepted compiled closures contain none.
5. **Original arbitrary TimeLaw:** retain the explicit scope distinction. No promise to prove the unchanged original statement is discharged by M's regularity premise. This is a mathematical limitation of the old representation, not an outstanding adapter for the certified endpoints.

For downstream work, import `RiffleLowerV2.Completed` (or the relevant lane Main module), retain the v1 target contract, and cite this independent receipt together with the coordinator's final audit manifest, v11 integration ledger, and `Contracts/dependencies/COMPLETED-v1` receipt. No new mathematical contract version or assumption was needed for E/M during this audit.

## Counterexample to deleting integrability

Fix k=2, T=10, eta=1/2. Any finite selected partition contains two distinct rational profiles p=(a,1−a) and q=(b,1−b), with 1/3<a<b<1/2, in one cell. Let μ_t switch between their point masses on a non-Lebesgue-measurable subset of (0,10). Every cell-mass function is constant, but the maximal-cost function is a nontrivial two-valued nonintegrable function. Its totalized interval integral is zero, so macroBeta=1.

For arbitrarily large N divisible by p's denominator, take every finite column exactly p. Lattice counting gives AlmostLike's error at most 1/log N, for any positive frequency tolerance. With chiGood=1/4 and gamma=1/2, LocalGood holds for each fixed positive rho once rho log N≥2. These cuts satisfy the proposed no-regularity version's numerical and counting premises.

Two labeled rows match in a single column with probability

```text
(N(a²+(1−a)²)−1)/(N−1) ≤ a²+(1−a)² < 5/9.
```

Column independence and a union bound give full-word collision probability at most `binom(N,2)(5/9)^floor(10 log N)`, tending to zero since `2+10 log(5/9)<0`. With no collision the equality graph is empty, and the proved graph-mixture representation is uniform. Thus TV is bounded above by this vanishing collision probability along the denominator subsequence, contradicting the claimed uniform eventual lower bound. The full quantifier and measurability checks are in all three independent reports. M's explicit scalar-integrability condition excludes this profile.
