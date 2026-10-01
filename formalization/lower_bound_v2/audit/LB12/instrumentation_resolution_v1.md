# LB12 instrumentation resolution review v1

This is a read-only source review of the proposed final verifier. No Lean build was run and no proof, output cache, or verifier source was changed. Reviewed fingerprints:

| File | SHA-256 |
|---|---|
| `audit/LB12/generate_check_v4.py` | `ef812855fd047526bc2e330d62fda7cab466fa843cff067c678dcf94719657cd` |
| `audit/LB12/verify_final_v1.py` | `d3ee17419d5d2b5e13fec603187232e02eab07805fee11c24b680a6f1a4bda50` |
| `scripts/full_check_v1.py` | `0cb43d59a44e9b9ff7db783573fc6a3a9d112b7167ea909530e509f904d28bba` |
| `audit/LB00/full_package_v1/FullCheck.lean` | `ada40e27428ee1ad26dd69e1562d8f116ede6eebca564f3baa2392c1901ee9c2` |

## Prior findings resolved in the LB12 verifier

- **Metadata closure:** v4 uses `ConstantInfo.getUsedConstantsAsSet` in both the direct-dependency record and recursive queue, including inductive constructors and recursor-family metadata. It uses the private environment view and records opaque declarations explicitly. `verify_final_v1.py` compares the recursive and collected axiom sets and enforces the three-foundation whitelist.
- **Owner modules:** the final verifier checks every required export's actual defining module against the owner's exclusive proof directory, and writes that evidence into the export ledger. The exact Lean type check remains the strong `isTheorem && type.isConstOf target` check.
- **Separate umbrella environment:** the final verifier creates a separate source importing only `RiffleLowerV2.Completed` (plus Lean instrumentation), checks all 58 frozen exports, and requires all lane Main entry points among the resulting imports. The additive Completed umbrella is the appropriate solution because the original foundation umbrella is frozen. The independently inspected `COMPLETED_UMBRELLA_COMPARISON_v1.md` makes that distinction explicit.
- **Whole-process success:** the final marker is now after the forward/inverse-TV example and all prints. `run_lean` requires return code zero and records `PROCESS_EXIT`; warnings are errors. The material structure and predicate prints requested in the prior review were added.
- **Source/build inventory:** the fresh source snapshot contains 183 modules, exactly the original 182-module LB12 snapshot plus `RiffleLowerV2.Completed`. The final verifier compares this set with current source discovery and requires every module in the build provenance's fresh-built list. It also checks the old source baseline, frozen manifest members, current dependency receipts, and 364 frozen foundation declarations. The baseline's recorded errors array is currently empty, and the old compiled-declaration inventory itself is protected by the frozen manifest.

These changes resolve the substantive defects previously identified in the LB12 checker. The preliminary v3 closure counts reported by the coordinator are not substituted for a successful final v4 run.

## Concrete blocking bug in the prerequisite coordinator audit

The coordinator's generated `audit/LB00/full_package_v1/FullCheck.lean:318` is syntactically corrupted. Its source generator ends the template with:

```python
.replace('PAIRS', pairs).replace('MODULES', module_list)
```

The second replacement also matches the literal log tag `IMPORTED_MODULES_JSON`. The generated Lean line consequently begins:

```text
logInfo m!"IMPORTED_"Contracts.v1.AdditionalFinite", ...
```

and continues with the entire module list inserted inside the string literal. This is a directly observed generation bug, not a hypothetical concern. The fresh proof compilation can succeed, but this generated audit cannot produce the successful coordinator receipt required by `verify_final_v1.py`.

**Owner: LB00.** Use a unique delimited placeholder or a replacement restricted to the exact required-module array; keep the `IMPORTED_MODULES_JSON` tag unchanged. Preserve the failed generated file and issue a new, explicitly versioned corrected audit. There is no mathematical reason to discard a successfully completed clean proof build solely because this later audit source is malformed. Any reuse of that clean output must be documented with the completed build log, source inventory/provenance, unchanged output hashes, corrected audit command, and new immutable receipt. The LB12 verifier can then consume the corrected evidence location. Do not label the current coordinator audit successful.

The coordinator v1 manual endpoint graph still follows type/value edges only. That need not force another proof build: LB12's corrected metadata-inclusive graph is the independent final graph. Distinguish the coordinator's narrower graph from LB12's complete declaration closure in release wording.

## Remaining final-verifier coverage gaps

### R1. Fingerprint the paths that the final Lean process will actually load

`verify_final_v1.py` checks each stored `resolved_path` in the coordinator's `imported_objects.json`, but does not verify that the current isolated-output module path still resolves to that stored path. Hashing an unchanged old target does not detect a retargeted symlink in the isolated library tree. This matters especially for the pinned third-party cache links. No such retargeting was observed in this review; the issue is that the implementation's claim of checking the final process's loaded object closure is slightly stronger than its check.

For every imported module and each recorded companion suffix, reconstruct the lookup path under the isolated library tree, falling back to the pinned runtime tree in the same order as the coordinator. Require both its current resolved path and hash to match the recorded entry. Repeat the checks after the independent and umbrella Lean processes before writing the success summary. Project and dependency source hashes should likewise be rechecked at that final boundary. This supplies a concrete binding between the observed environment and the fingerprint inventory.

### R2. Compare the independent environment's imports with its inventory

The v4 Lean checker emits `MODULES_JSON`, but `verify_final_v1.py` never parses it. It also generates `check_inputs_VERSION.json` without comparing that file with the fresh-build inventory. Source discovery and explicit generated imports already provide substantial coverage, so this is not a demonstrated missing import in the present files. Still, the intended independently reproducible module receipt should assert:

1. generated module set equals the current/fresh source-module set;
2. every generated module occurs in the independent Lean environment;
3. every actual imported module has a recorded object provenance entry (or an explicit, independently fingerprinted runtime fallback).

Record the actual independent import list in the final evidence. This prevents the final claim from depending only on the coordinator's earlier import inventory.

### R3. Distinguish independently rechecked source closure from trusted coordinator evidence

The final verifier rehashes `build_provenance.json` sources. The builder stops traversing third-party imports once an existing pinned library object is found, so that source list is smaller than the coordinator's full `imported_sources.json`. The latter file is protected by the coordinator evidence manifest, but the final verifier does not currently rehash each source it names. If the final summary claims all imported source files were independently rechecked, explicitly check that full inventory too; otherwise state that the wider library-source check is inherited from the verified coordinator receipt. This is a provenance-labeling issue, not evidence of any changed library source.

## Small reproducibility improvements

- Assert `before['errors'] == []` before treating the initial snapshot as accepted, even though it is empty in this run.
- Compare the exact-export map against all required name/target pairs, not just cardinality 58; the present frozen ownership file and per-declaration checks already make this safe for the inspected generator.
- Derive the saved module graph from the final source inventory rather than the original inventory plus one hard-coded Completed entry. The current graph is accurate because Completed is the only addition, but a future legitimate additive module would pass source/build checks and be omitted from that graph.
- The verifier does not itself wait for the coordinator receipt; it reads it immediately and fails if absent. Invoke it only after the corrected coordinator receipt exists, or describe the waiting as coordinator behavior.

## Resolution status

The final LB12 checker has corrected the earlier dependency, owner, umbrella, and completion-marker defects. Acceptance is pending the actual final run, repair of the directly observed coordinator template bug, and resolution or precise disclosure of R1–R3. No new mathematical premise or proof-source repair is requested by this review.
