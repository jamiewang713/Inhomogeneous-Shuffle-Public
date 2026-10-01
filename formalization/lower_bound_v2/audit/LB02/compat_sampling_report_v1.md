# LB02 concrete sampling bridges

The frozen export `RiffleLowerV2.Thinning.hypergeometricTransform : RiffleLowerV2.Targets.HypergeometricTransform` is proved in `RiffleLowerV2/Thinning/Sampling.lean`. It keeps the exact M>0, x≤M, m≤M, and all-s>0 frozen domain. Import `RiffleLowerV2.Thinning.Sampling` for the permutation bridge and `RiffleLowerV2.Thinning.ColumnSampling` for the actual shared column bridge.

`permutation_subset_expect` proves that the image of any deterministic subset B under a uniform permutation has the actual uniform `Compat.sampleLaw`. For any two subsets of B's cardinality, a permutation mapping one to the other induces an equivalence of the corresponding fibers of the map from permutations to subsets. The finite uniform equal-fiber expectation theorem then proves the law identity. `permutation_intersection_transform` specializes the arbitrary-marked-set all-s transform to any A and B. The frozen `hypergeometricTransform` follows by taking A and B to be the first x and m labels and proving the exact inverse-permutation membership formula. No assumed distributional equality is left in that export.

`columnRelabelEquiv` proves that every permutation of the row labels preserves the complete fixed-histogram column assignment space: all digit counts are checked. `columnDigitSubset_relabel` relates the actual selected-digit fiber to its permuted image. Equal fibers, proved with this equivalence and transitivity on equal-cardinality subsets, yield `column_subset_expect` for the actual `TimeProfile.columnPMF`. Its real-expectation identity is uniform over all digits, cuts, and columns, including zero and full digit counts.

The concrete one-step column export is:

```lean
theorem RiffleLowerV2.Thinning.column_intersection_transform
    {k N K : ℕ} (cuts : TimeProfile.Cuts k N K)
    (j : Fin K) (a : Fin k) (A : Finset (Fin N)) {s : ℝ} (hs : 0 < s) :
    RiffleLowerV2.expect (TimeProfile.columnPMF cuts j)
      (fun c => s ^ (A ∩ (Finset.univ.filter (fun i => c.val i = a))).card) ≤
      (1 - (cuts.count j a : ℝ) / N +
        (cuts.count j a : ℝ) / N * s) ^ A.card
```

This statement has neither a row-independence premise nor an unproved generic transform premise. It applies to arbitrary deterministic A, which is the required interface for exact column-by-column conditioning/backward affine recursion. The helper also covers N=0; no frozen domain is changed.

The initial Sampling proof candidate was supplied by the root agent. Fixes made here were explicit universe finset types, normalization of finite-subtype cardinals to reconcile distinct decision procedures, and exposure of the two uniform-law definitions before rewriting. The ColumnSampling proof is new. No shared file, target contract, original package, or existing freeze was modified.

Successful command from the package directory:

```text
python3 scripts/lane.py LB02 RiffleLowerV2.Thinning.Compat.SamplingCheck
```

`compat_column_build_v2.log` records successful compilation of both bridge modules and an exact-type/closure audit. The six inspected public bridge declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. Earlier failed audit execution and read-only development checks are preserved separately. `compat_sampling_receipt_v1.json` records exact elaborated types, current source hashes, the command/log, and closure results. `compat_sampling_declarations_v1.json` contains the same six checked bridge types from the preceding successful read-only audit.

The successive-thinning recursion, prefix assembly, residual specialization, union bound, asymptotics, and maximal-word exports remain separately verified root/other-worker components; this bridge receipt does not substitute for their checks.
