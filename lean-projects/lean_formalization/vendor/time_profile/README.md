# Reviewed project dependency snapshot

These two files are copied from the existing `formalization/time_profile`
project. Their definitions, theorem statements, and hypotheses are unchanged.
`PROVENANCE.json` records the original and copied source hashes;
`COMPATIBILITY.patch` records the entire difference.

The original project declares Lean 4.33.1. This library uses the installed
Lean 4.19.0. Two import paths and two theorem proof implementations needed
the documented compatibility changes. All three agents reviewed the
unchanged mathematical statements and the replacement proof steps before
those proof changes were made. The original project files were not edited.

`Base.lean` and `Ambient.lean` compile using the pinned 4.19.0 runtime.
The dependency check suppresses only the unused-variable linter, so all
original theorem binders can be retained. Compiler errors and other warnings
still fail the check. Public results using these files are included in the
transitive axiom audit.

Only the finite definitions and theorems needed by S01–S05 are used.
In particular, the included `TimeLaw` definition still has no time
measurability field, and its integral definitions prove no analytic
replacement statement. `StableAt` is not used by the adapters.
