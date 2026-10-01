# LB-01 physical-law bridge implementation, v1

The physical-law subtask is complete at the Lean theorem level. This is an implementation record subsequent to `representation_review_v1.md`; it does not overwrite that pre-proof review or issue the lane's completed-input receipt.

The implementation began only after the coordinator's `audit/LB00/LB01_INTERFACE_ACK_v1.md` and the lane's `REVIEW_RESOLUTION_v1.md` were available. No shared definition, frozen target, manuscript, original package, toolchain, or dependency cache was changed.

## Checked source and export

Source: `RiffleLowerV2/Model/Physical.lean`.

SHA-256: `f28ece509eee906fe8d1bc5bd20d2a8a9aeaf883fb817364b4ff168ed25cc493`.

Direct import: `RiffleLowerV2.Model.FiniteLaws`.

Main export, with exactly the frozen target:

```lean
theorem RiffleLowerV2.Model.physicalMatrixBridge :
  RiffleLowerV2.Targets.PhysicalMatrixBridge
```

Expanded type:

```lean
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  RiffleLowerV2.physicalInverseLaw cuts = RiffleLowerV2.matrixLaw cuts
```

The proof covers all the frozen natural-number domains, including empty decks, empty time sequences, zero piles, and a degenerate alphabet where a `Cuts` value exists.

The concrete sample equivalence and its deterministic consequence are also exported:

```lean
def RiffleLowerV2.Model.physicalPullbackEquiv
    {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) :
    RiffleLowerV2.Sample cuts ≃ RiffleLowerV2.Sample cuts

theorem RiffleLowerV2.Model.stableSort_physicalPullback
    {k N K : ℕ} (cuts : TimeProfile.Cuts k N K)
    (ω : RiffleLowerV2.Sample cuts) :
    RiffleLowerV2.stableSort
      (RiffleLowerV2.Model.physicalPullbackEquiv cuts ω) =
    RiffleLowerV2.physicalInverse ω
```

## Source correspondence and proof chain

This discharges the first two paragraphs of the proof of `lem:ub-graph-representation`: physical interleaving inversion, reverse chronological application of inverse steps, pulling current-position assignments back to original labels, and earlier-column lexicographic priority with stable ties.

The implementation expresses the inverse process for a chronological list of times by a right fold. `physicalInverseList_foldl` proves, for an arbitrary initial deck, that this is exactly the inverse of the frozen forward left fold. Thus time reversal is proved from the independently defined physical process, not built into the matrix model by renaming it.

`sort_cons` proves the stable-radix identity for a head key and a list-valued tail key. The head key is primary, and original labels remain increasing when both head and tail agree. Its proof uses `Tuple.eq_sort_iff`, including the full tie clause.

For a time `j` excluded from a list `l`, `physicalColumnShear` is an actual equivalence of canonical samples. It changes column `j` by precomposition with the inverse sorting permutation of the tail rows. Its inverse precomposes with that sorting permutation. The proof establishes that updating column `j` leaves every tail row and its sorting permutation unchanged.

`physicalPullback` recursively pulls back the tail coordinates, then applies the head-coordinate shear. `physicalPullback_other` proves that this recursion fixes every column outside the time list. `physicalPullback_sort` then proves that sorting the transformed list-valued rows equals the chronological physical inverse on that list. This is the triangular column relabelling proposed in the review, implemented recursively rather than by numeric suffix indices.

`physicalRowList_full` identifies the complete chronological list key with the canonical `rowWord` vector's underlying list. `physicalListSort_full` transfers both monotonicity and the stable-tie clause, rather than only identifying the sorted values. Specializing the recursive equivalence to `List.finRange K` gives the two public declarations above.

Finally, `map_uniform_equiv` from `FiniteLaws` proves that the actual sample equivalence preserves `fixedCountPMF`. Mapping the deterministic equality through this invariant law yields `physicalMatrixBridge`. No graph-law identity, conditional independence assumption, or desired-conclusion predicate enters the argument.

## Verification and independent review

Executed from `formalization/lower_bound_v2` through the required serialized wrapper:

```text
python3 audit/LB01/compile_lane.py RiffleLowerV2.Model.Physical
```

Final execution returned exit code 0 and exactly:

```text
LB01 BUILD_OK
```

This recompiles `FiniteLaws` and `Physical` into the isolated LB-01 output area. Earlier unsuccessful elaboration attempts exposed only API/transparency issues and were corrected; they are not certification results. The new module has no source proof placeholders, custom axioms, or native proof oracle. The final combined lane axiom audit must include `physicalMatrixBridge` and `stableSort_physicalPullback`; its printed closure is intentionally not claimed here before that audit runs.

The hypotheses/counterexample reviewer independently read the implemented proof and reported:

> Chronology and priority are correct: the right fold gives tail inverse composed with head sort, matching frozen forward-fold inversion. The recursion leaves the head unchanged; the head shear leaves the tail unchanged. The final pointwise theorem applies the actual pullback equivalence, so it avoids the raw-sample counterexample.

No mathematical issue was found. The pre-proof finite enumeration remains diagnostic support only; the completion claim here rests on the successfully compiled concrete equivalence and theorem.

## Dependencies and downstream use

All mathematical helper dependencies of the physical-law theorem are proved in the new module or in `FiniteLaws`/trusted imported sources. No physical-law premise remains pending. Import `RiffleLowerV2.Model.Physical` to use the export. The lane coordinator remains responsible for its umbrella import, combined axiom/signature audit, graph-law obligations, final build log, and completed-input receipt.
