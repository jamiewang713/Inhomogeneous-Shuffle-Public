# Stable-block Lean formalization

The assigned finite stable-block decomposition is implemented and kernel-checked with Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0). The final verifier checks 11 modules and audits all 153 project theorems. There are no proof placeholders or new project axioms. The only logical axioms appearing in theorem dependencies are Lean/mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`.

The mathematical inputs are exactly the three requested files. The original files are unchanged, and their hashes are checked on each verification run.

## Main results

- `Riffle.stable_partition` and `Riffle.stable_intervals_partition` in [SourceStable.lean](Riffle/SourceStable.lean) prove the retained-pair partition, its unique-prefix property, antichain, and disjoint convex sampled intervals.
- `Riffle.global_boundary_decomposition`, `Riffle.retained_stable_existsUnique`, `Riffle.global_stable_disjoint`, and `Riffle.omitted_iff_inadmissible` in [Global.lean](Riffle/Global.lean) prove exact admissible coverage and unique indexed cylinders.
- `Riffle.rawPair_retained` in [Retention.lean](Riffle/Retention.lean) proves the missing bridge in the source sketch: every compatible boundary pair is retained. Its nonterminal proof constructs a legal word on each side of a genuine crossing.
- [Boundary.lean](Riffle/Boundary.lean) proves first-crossing minimality, terminal fallback, left/right antichains, admissible subfamilies, joins, and pair fibers.
- [Pieces.lean](Riffle/Pieces.lean) proves disjoint lexicographic side decompositions and continuation invariance of the exact fluctuation quantities.

Terminal crossings, the empty ambient root at horizon zero, probability-one columns, zero piles, exact threshold equality, and fallback singletons are included. A singleton stable family is not assumed to be the singleton join. Sampled intervals may be empty.

## Contract and audits

[The frozen specification](spec/FROZEN_SPEC.md) records every assumption, definition, and theorem schema before project Lean code was written. [The freeze record](spec/freeze-record.json) contains the immutable source/specification hashes. The three independent reconstruction, representation, and adversarial reviews are in [reviews](reviews/). The final independent audit is [final-audit.md](reviews/final-audit.md).

The freeze record preserves the specification's original path before this package was moved into `formalization/stable_blocks`. Verification resolves that entry to the unchanged `spec/FROZEN_SPEC.md` in this directory.

[PROOF_MAP.md](PROOF_MAP.md) gives the complete upper/lower/random-pile proof structure and semantic dependencies for all 70 active named article declarations. [The source index](spec/dependency-index.md) records literal source references. [kernel-dependencies.json](kernel-dependencies.json) records actual Lean declaration dependencies for this package; [theorem-manifest.json](theorem-manifest.json) lists all audited theorem names.

## Verification

From this package directory, run:

```sh
python3 scripts/verify.py
```

The script rechecks the frozen inputs, rejects prohibited proof escapes, compiles every project module, audits all theorem axioms, and regenerates the declaration dependency graph. It uses the locally installed pinned compiler/mathlib under `.tooling`, or a standard installation and `.lake/packages/mathlib` when `.tooling` is unavailable. `check-file.sh` is the single-module checker. Compiler objects are ignored by version control.

For a fresh environment, install the compiler specified by `lean-toolchain`, resolve the pinned `lakefile.toml`/`lake-manifest.json` dependencies, and download the matching mathlib cache. The checked-in package can also be built as a Lean library with `lake build` in such an environment. The verification method used for this delivery is the explicit compiler invocation in `check-file.sh`; no native executable is needed.

Final results are in [verification.json](verification.json), [build.log](logs/build.log), and [axioms.log](logs/axioms.log).

## Scope and source issue

This package formalizes the assigned finite decomposition. It does not formalize the full cutoff theorem, the analytic estimates, or the random-pile mixing extension. Exact expected counts are encoded as the finite one-row product-mass formula. An integral identity connecting that formula to a separately constructed random fixed-column matrix probability space is an identified future foundation, not a declared or assumed theorem here.

The original anti-concentration lemma has a downstream obstruction: with equal deterministic three-pile first-column counts, the middle first-digit block has deterministic endpoints, while the article's side maxima give a positive exponent. This defeats the claimed endpoint anti-concentration for that block. The older fixed-column paper excludes the first column from the corresponding fluctuation maximum. This issue is documented in [the adversarial review](reviews/adversarial.md); the assigned definitions have been preserved exactly, and the structural theorems do not import that estimate.
