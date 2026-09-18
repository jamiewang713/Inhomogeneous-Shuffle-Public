# Isolated TimeProfile compatibility review

The import-only investigation below is retained as a record of the
failed first attempt. The subsequently approved proof-only adjustments
have now both compiled. The final hashes, exact diff, preserved
declaration checks, and scope are recorded in
`reviews/source_dependency_compatibility.md` and
`reviews/source_dependency_compatibility.patch`.

This review concerns a temporary copy of `Base.lean` and `Ambient.lean`,
not the original TimeProfile project and not the checked core
`RiffleProfiles` library. No source adapter has been implemented by this
reviewer. Original files have not been edited.

The TimeProfile project targets a later Lean/mathlib version than the
core library. Therefore its source declarations must be checked again
under the core's pinned Lean 4.19.0/mathlib environment before being
imported. A source file that compiled under another version is not a
substitute for that check.

## Snapshot and exact import-only changes

Temporary snapshot:

`/private/tmp/riffle-compat-review-5fe795c5/RiffleTimeProfile`

Only these import lines were changed, each with the coordinator's
explicit authorization:

1. In `Base.lean`,
   `Mathlib.Analysis.Convex.StdSimplex` became
   `Mathlib.Analysis.Convex.Basic`.
2. In `Ambient.lean`,
   `Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset` became
   `Mathlib.Algebra.Order.BigOperators.Ring.Finset`.

The older `stdSimplex` definition was inspected: it is exactly the set
of finite nonnegative real coordinate vectors whose sum is one. Thus
the import substitution preserves the reviewed simplex interpretation.
The first import-only test did not modify any definition, theorem
statement, assumption, or proof body.

| File | Original SHA256 | Import-only snapshot SHA256 |
|---|---|---|
| Base | `07a9bbd867763d1fb3e817789d0116cea6c19a3e2a48b677e6b5066a886cfd24` | `f76007aefd9c4c0176b41454e975c1192dd00240c3148dd101a8bebe118d12aa` |
| Ambient | `75d4558ff24fa1fc18cd09b0b1c2d0ea33140195317686e963b36038226eeea8` | `a46e1afcf8a394722ebdd8f7ee3b138981c90e35e96929805aa5ed07a9bcb44e` |

Before the coordinator narrowed the check to Base/Ambient only,
unchanged Analysis/Digits copies were also placed in this temporary
directory. Their initial checks stopped at the missing Base dependency.
They were not subsequently checked or modified. They are outside the
compatibility result reported here.

## Import-only compilation result

The coordinator obtained the missing old-mathlib cache entries. With
the cache available:

- `Base.lean` compiles successfully, exit zero, with no diagnostics,
  using only its import-line change.
- `Ambient.lean` reaches proof elaboration but fails at two API
  differences. Import changes alone are insufficient.

The two substantive Ambient diagnostics are:

1. `Finset.prod_le_prod_of_subset_of_le_one` is unavailable under that
   name in the pinned older environment, in `prefixWeight_extension_le`.
2. `Real.log_prod hp` has the wrong argument order for the older API,
   in `cL_exact_mass_exponent`. In Lean 4.19.0 its explicit arguments
   are the finite set, the function, and the nonzero-factor proof.

There are also four unused-parameter warnings (`hlegal`, `hMK`, another
`hlegal`, and `hk`). They are lint diagnostics, not mathematical failures.
All original parameters remain present.

Full compiler output is retained in the temporary snapshot's
`Base.log` and `Ambient.log`. The import-only Ambient file must not be
reported as a successfully checked dependency.

## Independent approval of the proposed proof-only backport

The coordinator subsequently proposed two exact proof-only adjustments.
I approve their mathematical and representation content before any such
adjustment is made:

- Preserve the entire statement of `prefixWeight_extension_le`,
  including its existing `hlegal` argument. Prove
  `positions K 0 M = positions K 0 v union positions K v M` under the
  existing `v<=M`, prove disjointness, and split the product. Each tail
  factor lies in `[0,1]`, so the tail product is at most one. The prefix
  product is nonnegative, so multiplying by that tail cannot increase it.
  This route remains valid when `M>K`, `v>K`, or the added range is empty;
  it adds no premise such as `M<=K`.
- Replace only the proof invocation `Real.log_prod hp` with
  `Real.log_prod _ _ hp`. The inspected old API is
  `Real.log_prod (s : Finset alpha) (f : alpha -> Real)` followed by
  `forall x in s, f x != 0`. The already derived `hp` is exactly that
  nonzero-factor proof. This is an explicit-argument adaptation of the
  same mathematical log-product theorem.

These proposed changes do not alter any TimeProfile definition,
statement, assumption, or the S01–S05 candidate statements. They are
ordinary proofs from the same finite product facts and trusted log
identity. Their actual checked status must be recorded after the
coordinator authorizes them and the updated snapshot is compiled.

The distinction is therefore precise: Base's import-only copy is checked;
Ambient's import-only copy is not checked; the proposed proof-only route
is independently approved but is not asserted here to have compiled.
