# Riffle profile estimates: finite Lean library

This is an isolated Lean 4.19.0 library for the finite estimates underlying
the assigned profile-estimate and bad-profile-reduction arguments. It includes
checked replacement, entropy, weighted-tail, finite counting, and actual matrix expectation proofs.
The full source-model and asymptotic formalization remains incomplete;
`COVERAGE.md` distinguishes every proved part from its remaining obligations.

## Start here

- `PROOF_STRUCTURE.md`: upper bound, lower bound, random-pile extension, and
  required foundational interfaces.
- `DEPENDENCY_MAP.md`: intended semantic dependencies of all 70 active named
  declarations in the supplied TeX.
- `SOURCE_DEPENDENCIES.md`: declaration locations and literal reference graph,
  including the 11 declarations in the historical commented section.
- `FROZEN_FINITE_CONTRACT.md`: immutable definitions and F01–F20 statements.
- `FROZEN_SOURCE_ADAPTERS.md`: S01–S05, independently reviewed and frozen
  before applying the finite results to existing source definitions.
- `FROZEN_TRUNCATION_CONTRACT.md`: T01–T09, reviewed and frozen before connecting
  boundary and exceptional events to the actual fixed-column matrix law.
- `TRUNCATION_REVIEW_COMPARISON.md`: comparison of all three truncation reviews.
- `REVIEW_COMPARISON.md`: comparison of the independent reconstruction,
  representation, and counterexample reviews before implementation.
- `COVERAGE.md`: source-to-Lean mapping and unproved obligations.
- `PROJECT_INTERFACES.md`: newly available prior definitions, representation
  differences, and limitations of their current interfaces.
- `VALIDATION.log`: compilation and transitive dependency checks.

## Lean modules

| Module | Contents |
|---|---|
| `RiffleProfiles/Estimates.lean` | Finite costs, digit clauses, replacement, blocking, `c_L` decomposition, maximal mass, side masses, fluctuation logs, parent algebra. |
| `RiffleProfiles/Entropy.lean` | Finite Gibbs inequality, tilted entropy, zero-count cases, cellwise sums, bounded exceptional deletion. |
| `RiffleProfiles/Counting.lean` | Binomial tails, sparse labelled patterns, boundary and profile descriptor cardinalities. |
| `RiffleProfiles/WordMass.lean` | Inhomogeneous product word weights, generating and subset-tail estimates, coarse-fibre bound and counterexample. |
| `RiffleProfiles/SourceReplacement.lean` | Source regularity, finite `c_E` replacement, and finite maximal-pile bound for the source `c_L`. |
| `RiffleProfiles/SourceFluctuation.lean` | Source side maxima and extended-real `c_F` comparison with the exact ambient error. |
| `RiffleProfiles/ModelWordMass.lean` | Existing Model normalization, exact product-functional identities, event and union bounds. |
| `RiffleProfiles/BoundaryTruncation.lean` | Actual selected-prefix violations, strict floor cutoff, and boundary event tails. |
| `RiffleProfiles/ExceptionalTruncation.lean` | Exact exceptional-prefix event with arbitrary word-dependent endpoints and its tail. |
| `RiffleProfiles/BoundaryCounting.lean` | Injection of actual admissible boundary lists into finite descriptors; actual pair count. |
| `RiffleProfiles/MatrixLaw.lean` | Proved uniform-column symmetry, row marginals, full-word probability, and expected row counts. |
| `RiffleProfiles/MatrixTruncation.lean` | Boundary and exceptional-prefix expected-row bounds under the actual matrix law. |

`RiffleProfiles.lean` imports all twelve modules. The first four modules can be
used independently. The two source specializations use reviewed, checked
copies of `TimeProfile.Base` and `TimeProfile.Ambient` under
`vendor/time_profile`; their provenance and complete compatibility diff are
recorded there. The truncation modules use verbatim, separately compiled prior
project dependencies under `vendor/stable_blocks` and `vendor/shuffle_law`.
Their complete provenance is recorded in those directories. Other concurrent
modules are not presumed proved.

## Reproduce the checks

From the repository root, run:

```sh
python3 lean_formalization/check_all.py
```

The check uses the existing shared toolchain under `formalization/.tooling`
and writes compiled files only inside this directory. The package also
records Lean 4.19.0 and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b` in `lean-toolchain` and
`lakefile.toml`. The shared-toolchain check above is the validated build path.

No claim is made that another task's Lean files have been checked merely
because they occur in the shared workspace. The three mathematical source
files are unchanged; their hashes are recorded in `SOURCE_SHA256.json`.
