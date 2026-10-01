# Completed proof package integration receipt v1

FRESH_FULL_PACKAGE_BUILD_AND_AUDIT_PASSED. All 58 required frozen exports, empirical endpoint E, scalar-integrable macroscopic endpoint M, and the derived sequence corollary are coordinator-certified. LB12's independent final report is a separate certification step.

Use `import RiffleLowerV2.Completed`. It imports all eleven lane Main modules and the unchanged foundation. A separate environment importing only this completed umbrella verifies all 58 literal theorem types. The original RiffleLowerV2.lean, Contracts/v1, build.py, scripts/audit.py, Check.lean, README and every prior audit remain unchanged. See COMPLETED_UMBRELLA_COMPARISON_v1.md.

## Successful build and audit evidence

- Fresh output: `.build/full_package_v1/lib/lean`. It began absent; no shared or lane project object was copied. Only pinned third-party library caches are reused read-only.
- Exact build command/environment: `audit/LB00/full_package_v1/COMMANDS.json`; build log `audit/LB00/full_package_v1/build.log`; immutable source provenance `audit/LB00/full_package_v1/build_provenance.json`; pre-build hashes `audit/LB00/full_package_v1/source_snapshot.json`.
- Every one of the 183 package source modules, including diagnostics and both umbrellas, was rebuilt. Every reached canonical project module was also rebuilt. There were 197 source compilations total, with 14 nonfatal style warnings and no build errors.
- Accepted audit command: `python3 scripts/final_audit_v3.py --build-run v1 --run v3`. Exact Lean commands and LEAN_PATH are in `audit/LB00/final_audit_v3/COMMANDS.json`; successful logs are `audit/LB00/final_audit_v3/audit.log` and `audit/LB00/final_audit_v3/completed_only.log`. Both treat warnings as errors and have no diagnostics.
- Audit: 3216 declarations attributed using compiler module metadata, 58 exact required theorem types, all previous inventories unchanged, full ConstantInfo.getUsedConstantsAsSet traversal including constructor and recursor metadata. Recursive axiom sets agree with Lean.collectAxioms and contain only Classical.choice, Quot.sound, propext.
- Actual imported object/companion hashes and commit-checked source identities are in `audit/LB00/full_package_v1/imported_objects.json` and `audit/LB00/full_package_v1/imported_sources.json`.

The initial full_check_v1 audit generator had a diagnostic-string substitution error. Its source and failed log are preserved. The successful fresh source build was retained; the separately versioned corrected audit supersedes that instrumentation only. CORRECTED_AUDIT_v3.json makes the evidence routing explicit. No project proof was changed to repair the audit.

Reproduce the complete successful workflow with a new unused version label:

```text
python3 scripts/verify_completed_v2.py --run v4
```

The wrapper produces an initially absent fresh output tree and immutable new logs, then runs the corrected full and Completed-only checks. Existing evidence is never overwritten. Read-only registration check: `python3 scripts/check_dependency_receipt.py COMPLETED-v1`.

## Immutable receipts and scope

Fresh-build evidence manifest: `audit/LB00/full_package_v1/SHA256.json`, SHA-256 `e644816f9dc96092b7d28bf95d461d37bb6596cb6dd7211e9a565fea84a72dca`.
Full registry manifest: `Contracts/dependencies/COMPLETED-v1/SHA256.json`, SHA-256 `08eb5a4470c0b41afe691e2fa85e9dd9fe282ea9a8116b079cbbd11e06173181`.
Lean: Lean (version 4.33.1, arm64-apple-darwin24.6.0, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release); compiler SHA-256 `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554`; mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
Original frozen manifest SHA-256 `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`.

Exact exports are in COMPLETED_EXPORTS_v1.md and ledger v11. E has no temporal regularity premise. M requires scalar integrability of the chosen partition's cell masses, a and psi for alpha in [2,4], with the same partition in AlmostLike. Neither proof certifies the unchanged arbitrary-totalized-TimeLaw claim. The independently reviewed mathematical counterexample to deleting this premise is recorded by LB12 and is not a new Lean-certified refutation.
