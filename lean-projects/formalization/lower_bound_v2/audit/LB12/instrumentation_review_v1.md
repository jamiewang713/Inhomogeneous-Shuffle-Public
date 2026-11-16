# LB12 independent audit-instrumentation review v1

Reviewed `audit/LB12/generate_check_v2.py` and its generated `IndependentCheck_v2.lean`, plus the pinned Lean 4.33.1 implementations of `Lean.Util.CollectAxioms` and `Lean.Util.FoldConsts`. This is a source review; no build was run and no instrumentation was modified. The earlier failed v1 syntax attempt is historical evidence, not an accepted audit output.

## Verdict

The exact-export check and actual-module-based declaration classification are sound for their stated jobs, and the axiom whitelist is appropriately strict. The v2 manual dependency graph is not yet a complete declaration dependency closure: it omits inductive/recursor metadata edges. The planned `--all` import audit also cannot certify the umbrella's own reachability, because it imports proof modules directly. Address those two distinctions before calling the combined result a complete independent dependency and umbrella audit.

## Corrections needed for the claimed coverage

### I1. Add inductive and recursor metadata to the manual closure

At generator lines 85–86 the queue follows only `ci.type.getUsedConstants` and `ci.value?`. An inductive declaration generally has no `value?`, and its type need not mention any of its constructors. A reached structure type therefore need not cause the manual walk to inspect all constructor-field types. Similarly, recursor mutual-family metadata is absent from the traversal.

The pinned runtime itself treats these declarations specially. `Lean/Util/CollectAxioms.lean:66` traverses `inductInfo.ctors`; `Lean/Util/FoldConsts.lean:66–73` provides `ConstantInfo.getUsedConstantsAsSet`, adding inductive constructors and `recInfo.all` in addition to type/value constants. Use that helper for queue expansion, or add the corresponding metadata edges explicitly and expose them as a separate `metadata_dependencies` field in the declaration JSON. If retaining `type_dependencies` and `value_dependencies` for clarity, preserve both and record the extra edges rather than silently merging their meanings.

A simple reason this matters is an inductive type with a constructor field whose type refers to another project declaration: the inductive's own type may be just `Type`, so the current traversal can stop before the field's dependency. Such a field is exactly the kind of structure-contained assumption the LB12 prompt asks to inspect.

This finding does not itself demonstrate a missed forbidden axiom in the current package. `Lean.collectAxioms` does expand inductive constructors, and the generator applies it to every project declaration. Nevertheless, `all_reachable_names` and `recursive_axioms` must not be advertised as complete independently reconstructed closure data until metadata edges are included. Once corrected, compare sorted/deduplicated recursive and collected axiom sets and fail on disagreement, rather than merely printing both.

### I2. Check the umbrella in a separate import environment

The `--all` generator imports every discovered source module plus `RiffleLowerV2` and `Contracts`. This correctly makes all package modules available for auditing, but it cannot reveal that the umbrella omits one of those modules: the direct import makes the omitted theorem available anyway.

At review time `RiffleLowerV2.lean` imports only `RiffleLowerV2.Shared` and `Contracts.v1`. A separate checker must import only `RiffleLowerV2` and then verify all 58 frozen exports. That checker should run after the coordinator's reviewed umbrella correction. Preserve the all-module checker for the distinct coverage claim that every package module was inspected. One check cannot replace the other.

### I3. Bind exported declarations to their owner modules

The generator correctly obtains each declaration's defining module using `env.getModuleIdxFor?`; this is stronger than classifying by declaration namespace and correctly includes compatibility declarations and generated/private proof names.

However, the exact-export loop currently checks only existence, theorem kind, and target type. It does not assert that the declaration was defined inside its owner's exclusive proof directory. Add expected owner/module-prefix information from each `OWNERSHIP.json` lane and compare it with the actual defining module for every required export. For example LB10 exports must be defined under `RiffleLowerV2.EmpiricalLower`, and LB11 under `RiffleLowerV2.MacroscopicLower`. Log the actual module in `EXACT_EXPORT_JSON` as well. This is an audit-completeness improvement, not evidence of an existing ownership violation.

### I4. Make the successful-run criterion cover the whole checker

`LB12_INDEPENDENT_AUDIT_PASSED` is emitted before the forward/inverse-TV example and final `#print` commands. Require the Lean process to exit successfully with no errors in addition to seeing the marker, or move a final marker after all commands. Checking only the current marker could accept a run whose final orientation example subsequently fails. Warnings-as-errors should be supplied in the recorded invocation if that is part of the intended verification standard.

## Checks that are satisfactory, with precise limits

- **Exact frozen targets:** `ci.isTheorem && ci.type.isConstOf target` is deliberately stricter than checking pretty-printed text. For these zero-argument target constants it rejects extra universal hypotheses or a conclusion that is merely similar. A proof of a target constant still needs semantic auditing of that target's immutable body, which the separate contract/hash and hypothesis reviews supply. It does not by itself protect against a changed target definition, so retain the frozen-manifest validation.
- **All current exports:** the observed ownership inventory has 58 required exports and 58 distinct names. The non-`--all` v2 checker intentionally checks only six E/M-lane exports; it is an endpoint preflight. The generated final `--all` checker must be used for the full frozen-export claim.
- **Current source discovery:** recomputing the planned `--all` inventory without writing it finds 183 imports: all `.lean` files below `RiffleLowerV2/` and `Contracts/`, plus the two top-level umbrellas. These are all top-level package Lean roots observed. It includes check modules as well as Main modules, so it does not repeat the historical hard-coded-module omission. Audit scratch files are appropriately outside this package-module inventory.
- **Coverage receipt:** `MODULES_JSON` should be compared against the generated `check_inputs_VERSION.json`: require every intended import to be present, and record the difference between the package source inventory and imported project modules. The fresh builder must also record one successful compilation per intended source module. Successfully importing an old `.olean` alone is not a fresh-build receipt.
- **Axiom whitelist:** the allowed names are exactly `propext`, `Classical.choice`, and `Quot.sound`; custom axioms, `sorryAx`, and native-reduction proof axioms are rejected. Every project module declaration receives `collectAxioms`, not just the public theorem inventory. A project-declared axiom is rejected directly as well. The manual endpoint walk also ranges over all encountered module origins when rejecting axioms, rather than applying a project-prefix filter to that rejection.
- **Actual proof values:** `allowOpaque := true` requests theorem/opaque values for direct dependency extraction. For extra clarity, label `opaqueInfo` explicitly rather than the catch-all `generated`, and use the checked/private environment view consistently if needed by the pinned module API. Imported project sources here do not use the new `module` declaration form, so no currently observed hidden module body is identified by this review.
- **Recorded bodies:** the JSON `value` field is populated only when `ci.type.isSort`. That prints unparameterized target bodies, but not every parameterized predicate such as `GeometrySpec`, `WitnessSpec`, or `ScalarIntegrable`. The explicit `#print ScalarIntegrable` and manual source review cover the latter regularity premise. Do not describe the JSON as a dump of all proof terms or all structure-field bodies. For a self-contained statement audit artifact, add explicit prints of the material parameterized predicates/data constructors or link their hashed source files.
- **Root selection:** E, the cold endpoint, M, and M's sequence corollary are walked explicitly. E's value reaches `largestOnly`, so the largest branch is included in E's transitive closure. Listing `largestOnly` separately is optional convenience, not necessary for endpoint coverage.
- **Pinned-runtime metadata:** Lean 4.33.1's `collectAxioms` consults precomputed imported-module axiom metadata. The separate manual traversal is valuable as a second audit route; the clean source build and recorded runtime/mathlib hashes remain necessary to tie that metadata to the inspected sources. Do not call the axiom metadata alone independent reconstruction of every imported proof body.
- **Artifact preservation:** the generator uses exclusive-create mode for its checker and input manifest, preserving existing v1/v2 artifacts. Follow the same approach for corrective versions.

## Requested resolution record

The coordinator's final LB12 resolution should identify the corrected checker version, the metadata-edge fix, a separate umbrella-only export check, the full 183-module source/build comparison (or an explicitly explained updated count), all 58 exact-export results with owner modules, complete endpoint closure/axiom results, and the full process exit status. No new mathematical hypothesis or theorem change is required by this instrumentation review.
