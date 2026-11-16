# Current Theorem 1.1

This additive package connects the existing upper and lower bound developments
to Theorem 1.1 in `time_inhomogeneous_riffle_shuffle_lean_paper.tex`.
The canonical proof packages and the manuscript are left unchanged.

## Verification status

Verified on 2026-10-04 with Lean 4.33.1. `RiffleMain`, `Audit.lean`, and both
original `Completed` umbrellas build successfully. All seven public theorem
declarations in the final audit depend only on `propext`, `Classical.choice`,
and `Quot.sound`; the audit prints `MAIN_THEOREM_TRUST_OK` and rejects every
other foundation dependency. The seven build-driver regression tests pass.

The full printed theorem statements and audit output are saved locally in
`.build/main-theorem-audit.log`. Source-hash manifests for successful builds
and the audit are in `.build/receipts`.

The checked manuscript has SHA-256
`3ffceab6b7a0e9aaa063e771d4c90f0c64dca37c006053f87972acde65e5e8e1`.
The accompanying 48-page PDF has SHA-256
`f7c71646d410e136b8bb4630dd2f0df0133ab89a0aabebeab1f2d3468f826b70`.

## Entry points

`RiffleMain.theorem_1_1` combines all three assertions in one declaration.

| Manuscript assertion | Lean declaration |
| --- | --- |
| Fixed positive horizon away from the critical time | `RiffleMain.main_random_sequence` |
| Both cutoff limits when the critical time is finite | `RiffleMain.cutoff_random_sequence` |
| Every finite horizon stays unmixed when the critical time is infinite | `RiffleMain.infinite_critical_random_sequence` |

These declarations are in `RiffleMain/Process.lean`. They allow arbitrary
probability spaces for the random infinite cut sequences, require measurable
finite prefixes, and use the averaged chronological physical forward law.
There is no independence assumption on the cut columns. Uniform interleavings
conditional on the count array are encoded by the existing physical law.

`RiffleMain/Main.lean` contains the corresponding finite-marginal statements.
`RiffleMain/ProcessModel.lean` connects probability measures on the original
spaces to these finite marginals.

## Proof bridges

* `RiffleMain/Profile` (Lemma 2.8, PDF pp. 10–12): the manuscript's continuous-test convergence in
  probability implies uniform interval-cost errors and local goodness with
  fixed positive parameters. Measurability supplies scalar integrability.
* `RiffleMain/RandomLower` (Corollary 6.22, PDF pp. 46–47): one event distinguishes all admissible count
  arrays, so the lower bound survives averaging over dependent columns. The
  null probability pays for the finite union over all count arrays.
* `RiffleMain/Critical` (Lemma 2.2, PDF p. 7, and the main proof on p. 48): strict margin decay, signs on either side of the
  extended critical time, positivity of that time, and cutoff horizons.
* `RiffleMain/MarginEvents.lean` and `RiffleMain/Limits.lean`: transfer the
  profile margins to the empirical endpoints and derive the two TV limits.

Profiles are defined on nonnegative times. Their extension to negative times
is only used to reuse the existing interval-integral interface; every
integral in the theorem uses nonnegative endpoints.
Time carries its Borel sigma algebra: every Borel subset of the simplex has
a measurable evaluation map. Local nondegeneracy is an almost-everywhere
positive lower bound on each bounded time interval.

## Reproduce

The package pins Lean 4.33.1 and mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`.
After installing the pinned dependencies with `lake update`, run from this
directory:

```text
python build.py RiffleMain
python build.py --run Audit.lean
python build.py RiffleUpperV2.Completed RiffleLowerV2.Completed
python -m unittest -v test_build.py
```

`build.py` resolves the canonical source modules without writing to their
packages. It compiles project modules into `.build/lean`, checks source hashes
and dependency freshness, and records successful invocations in
`.build/receipts`. Use `--fresh` to recompile all project sources in a requested
dependency closure. Failed rebuilds invalidate the earlier module receipt;
source changes during compilation or while waiting for a shared lock cause an
error. The driver rechecks all visited project sources and receipts before
reporting success. Audit source hashes are also included in the final receipt.
The regression tests exercise these cache and source-change checks using a
mock compiler; the separate Lean builds above check the mathematical proofs.

The custom build command is required because the original proof libraries are
kept in separate frozen directories; `lake build` alone does not configure
those source roots.
