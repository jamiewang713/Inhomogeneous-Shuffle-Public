# Base/Ambient dependency compatibility verification

The isolated copies of `RiffleTimeProfile.Base` and
`RiffleTimeProfile.Ambient` compile successfully with Lean 4.19.0
(`6caaee842e94`) and mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Every declaration name,
theorem header, assumption, definition body, and structure field is
preserved. The changes consist of exactly two import substitutions and
two approved theorem proof adjustments. The original source files were
not edited.

The final snapshot is
`/private/tmp/riffle-compat-review-5fe795c5/RiffleTimeProfile`.
The coordinator subsequently copied these exact bytes into
`lean_formalization/vendor/time_profile/RiffleTimeProfile`; I checked
both vendored hashes against the snapshot. The complete unified diff is
in `reviews/source_dependency_compatibility.patch`.

## Exact changes and approval scope

1. Base replaces `Mathlib.Analysis.Convex.StdSimplex` with
   `Mathlib.Analysis.Convex.Basic`. In the older environment, the latter
   contains the finite standard simplex definition used by this file.
2. Ambient replaces
   `Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset` with
   `Mathlib.Algebra.Order.BigOperators.Ring.Finset`. The first path does
   not exist in the pinned older mathlib; the second provides the
   finite product bounds needed here.
3. Only the proof body of `prefixWeight_extension_le` is replaced.
   It splits `positions K 0 M` as the disjoint union of
   `positions K 0 v` and `positions K v M`. The tail product is at most
   one and the prefix product is nonnegative, yielding the original
   inequality. Its original binders, including `hlegal`, remain
   verbatim. In particular, no assumption `M ≤ K` or additional
   positivity hypothesis has been added. The argument also covers
   empty ranges and depths beyond `K`.
4. In the proof of `cL_exact_mass_exponent`, the invocation
   `Real.log_prod hp` becomes `Real.log_prod _ _ hp`, supplying the
   finite set and function arguments required by the older API. The
   existing factor nonvanishing proof `hp` is unchanged.

The coordinator authorized both import changes. After the import-only
Ambient compile exposed two proof API incompatibilities, three
independent reviewers approved these exact proof routes before their
implementation in the snapshot. No source statement or frozen finite
contract was changed to obtain compatibility.

## Preservation verification

A mechanical check reconstructed each snapshot from its original using
only the approved replacements, asserted each replacement occurred
exactly once, and asserted byte-for-byte equality with the snapshot.
It also compared top-level declaration inventories, every theorem
header before its proof, and every complete non-theorem declaration.

| File | Identical theorem headers | Identical complete non-theorem declarations | Changed theorem proof bodies |
|---|---:|---:|---|
| Base | 24 | 37 | None |
| Ambient | 9 | 17 | `prefixWeight_extension_le`, `cL_exact_mass_exponent` |

The non-theorem comparison includes definitions, abbreviations and
structures. Namespace commands, options, variables, comments, and all
other code are unchanged by the exact replacement check. This is a
textual preservation check plus kernel compilation under the pinned
environment; it does not claim equality of all internals of the two
mathlib releases.

| File | Original SHA256 | Final snapshot and vendor SHA256 |
|---|---|---|
| Base | `07a9bbd867763d1fb3e817789d0116cea6c19a3e2a48b677e6b5066a886cfd24` | `f76007aefd9c4c0176b41454e975c1192dd00240c3148dd101a8bebe118d12aa` |
| Ambient | `75d4558ff24fa1fc18cd09b0b1c2d0ea33140195317686e963b36038226eeea8` | `329493e3ef2d0b03a12c1beba07117e93383cbe572984bf79f323866b7c507d2` |

The original hashes were rechecked after the completed compilation and
match the pre-edit originals. The mechanical check result is retained
at `/private/tmp/riffle-compat-review-5fe795c5/preservation-verification.json`.

## Compilation and diagnostics

Both files were compiled separately, in dependency order, using the
workspace's pinned Lean executable and the snapshot root first in
`LEAN_PATH`, followed by the pinned mathlib library and its package
libraries. Both commands returned exit status zero and produced their
`.olean` files. Base produced no diagnostics. Ambient produced only
these six unused-variable warnings:

| Snapshot line | Retained binder |
|---:|---|
| 91 | `hlegal` |
| 95 | `hlegal` |
| 120 | `hMK` |
| 138 | `hlegal` |
| 148 | `hMK` |
| 178 | `hk` |

The final compiler logs are
`/private/tmp/riffle-compat-review-5fe795c5/Base.log` and
`/private/tmp/riffle-compat-review-5fe795c5/Ambient.log`.
No binder was removed to silence a warning. The coordinator's vendor
checker retains `warningAsError=true` and disables only
`linter.unusedVariables` for these dependency copies through a compiler
flag; this does not modify the source files or theorem assumptions.
The original core library's strict checker options remain in force.

This result covers only Base and Ambient. Initial unchanged copies of
Analysis and Digits in the temporary directory were not successfully
checked after the task narrowed to these two dependencies. This review
does not establish analytic or stochastic bridges, time measurability,
or any source-adapter theorem. Those are separate obligations. No
adapter code was written by this compatibility reviewer.
