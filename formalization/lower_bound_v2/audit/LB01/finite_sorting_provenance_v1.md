# LB-01 finite-law and sorting implementation provenance, v1

The hypotheses reviewer implemented `Model/FiniteLaws.lean` after the LB-00 additive-interface acknowledgement and the lane's review comparison. The coordinator later handed over `Model/Sorting.lean` to resolve its concrete predicate-instance elaboration failure. Neither proof file alters a frozen target or shared definition.

## Checked exports

All names below have prefix `RiffleLowerV2.Model`.

| Declaration | Exact target type |
| --- | --- |
| `columnIndependence` | `RiffleLowerV2.Targets.ColumnIndependence` |
| `rowRelabeling` | `RiffleLowerV2.Targets.RowRelabeling` |
| `inversionTV` | `RiffleLowerV2.Targets.InversionTV` |
| `stableTie` | `RiffleLowerV2.Targets.StableTie` |
| `prefixRanks` | `RiffleLowerV2.Targets.PrefixRanks` |

These are proved declarations, not target predicates. Their domains remain the complete frozen domains: arbitrary natural `k,N,K` and every `Cuts k N K`. In particular, no positive-deck, positive-pile or alphabet-size premise was added.

The explicit uniform-column marginal is also checked, in addition to the frozen independence target:

```lean
columnMarginal {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K) :
  (fixedCountPMF cuts).map (fun ω => ω j) = columnPMF cuts j
```

Its proof selects one indicator coordinate in the product-expectation identity and sets every other coordinate function to one. Equality of all real-valued atom masses implies equality of PMFs because their masses are finite. This also exports generic `expect_const` and `expect_singleton` helper lemmas.

Additional exact finite-law API:

```lean
expect_uniform {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
  expect (PMF.uniformOfFintype α) f = (∑ a, f a) / Fintype.card α

map_equiv_apply {α β : Type*} [Fintype α]
  (P : PMF α) (e : α ≃ β) (b : β) :
  (P.map e) b = P (e.symm b)

map_uniform_equiv {α β : Type*} [Fintype α] [Fintype β]
  [Nonempty α] [Nonempty β] (e : α ≃ β) :
  (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β

uniform_expect_equiv {α β : Type*} [Fintype α] [Fintype β]
  [Nonempty α] [Nonempty β] (e : α ≃ β) (f : β → ℝ) :
  expect (PMF.uniformOfFintype α) (fun a => f (e a)) =
    expect (PMF.uniformOfFintype β) f

expect_bind {α β : Type*} [Fintype α] [Fintype β]
  (P : PMF α) (Q : α → PMF β) (f : β → ℝ) :
  expect (P.bind Q) f = expect P (fun a => expect (Q a) f)

expect_map {α β : Type*} [Fintype α] [Fintype β]
  (P : PMF α) (g : α → β) (f : β → ℝ) :
  expect (P.map g) f = expect P (fun a => f (g a))

uniform_pi_expect_prod {T : Type*} [Fintype T] {A : T → Type*}
  [∀ t, Fintype (A t)] [∀ t, Nonempty (A t)] (f : ∀ t, A t → ℝ) :
  expect (PMF.uniformOfFintype (∀ t, A t)) (fun ω => ∏ t, f t (ω t)) =
    ∏ t, expect (PMF.uniformOfFintype (A t)) (f t)
```

The canonical relabeling API is:

```lean
columnEquiv (cuts : Cuts k N K) (j : Fin K) (σ : Permutation N) :
  ColumnAssignments cuts j ≃ ColumnAssignments cuts j

sampleRelabel (cuts : Cuts k N K) (σ : Permutation N) :
  Sample cuts ≃ Sample cuts

columnEquiv_apply_val cuts j σ a i :
  (columnEquiv cuts j σ a).val i = a.val (σ i)

sampleRow_relabel cuts σ ω i :
  sampleRow (sampleRelabel cuts σ ω) i = sampleRow ω (σ i)

rowWord_relabel cuts σ ω i :
  rowWord (sampleRelabel cuts σ ω) i = rowWord ω (σ i)

sampleRelabel_uniform cuts σ :
  (fixedCountPMF cuts).map (sampleRelabel cuts σ) = fixedCountPMF cuts
```

The value lemmas are simplification lemmas. Relabeling always precomposes by `σ`; the inverse equivalence precomposes by `σ.symm`.

## Source provenance and representation changes

The new module works directly on the canonical PMF sample space. It does not import the legacy `FiniteLaw`, `ColumnRandomness`, or permutation-column construction, and no legacy theorem is used without rechecking its proof on the new objects.

The proof of `uniform_pi_expect_prod` adapts the finite product-sum calculation in `RiffleLower.uniform_pi_expect_prod` (FixedColumns M02). The old theorem has the same dependent types and real-valued product integrand but uses `RiffleLower.expect (RiffleLower.uniformLaw ...)`; the new theorem uses shared `RiffleLowerV2.expect (PMF.uniformOfFintype ...)`. The proof-only change is replacing the expectation-to-average lemma with the directly checked PMF version. `columnIndependence` separately specializes by the shared `fixed_expect_eq_average`, so no sample-space identification is assumed.

Similarly, `uniform_expect_equiv` follows FixedColumns M01's cardinality-preserving reindexing proof. The old signature has `RiffleLower.uniformLaw`; the new signature above has `PMF.uniformOfFintype`. The expected-value formula itself is re-proved from the canonical PMF mass, including its `ENNReal.toReal` conversion. The helper `expect_map` is re-proved through the checked `expect_bind`; it does not reuse the old real-law `mapLaw` construction.

`stableTie` applies the actual mathlib characterization `Tuple.eq_sort_iff` to shared `stableSort` and `rowWord`, the same direct mathematical step used in legacy Sorting S2. `prefixRanks` follows the foundations M07/M08 monotone-list and finite-set-difference argument, with raw shared prefixes and unsorted shared counts. Direct `card_bij` proofs reindex those counts by the shared sorting permutation. Explicit finset extensionality reconciles concrete and generic decidable-predicate instances; this changes no mathematical statement.

Original source SHA-256 values:

| Source | SHA-256 |
| --- | --- |
| `lean-lower-bound/RiffleLower/FixedColumns.lean` | `f7b9827fb59064ba817bb2f40c778218b6e8b041a0448561cc375dbfbd27018d` |
| `lean-lower-bound/RiffleLower/FiniteProbability.lean` | `1918946b462cfec9183ddcd50280abbe65185b89a65de8064a9884559fde276a` |
| `lean-lower-bound/RiffleLower/Sorting.lean` | `3e0ade77a5b306f6d0eea3c876206180e0230394dd16b5058360b3f2b5ffa656` |
| `formalization/foundations/RiffleShuffle/Matrices.lean` | `2a674866084434aa87978a35af366251df362fa0f9873b4493c136aa69e3c317` |

New source SHA-256 values at this handoff:

| Source | SHA-256 |
| --- | --- |
| `RiffleLowerV2/Model/FiniteLaws.lean` | `cc5abe4ecf21f682658ca77e7a867368a4f1f8c4ab0b9d70eba79a9041772a06` |
| `RiffleLowerV2/Model/Sorting.lean` | `ab2e2fd9f105ab4fac52f6764d731aad7a93a34f5cb6cd85660b67eacd595a54` |

## Successful build records

From `formalization/lower_bound_v2`, both commands completed with exit code 0:

```text
$ python3 audit/LB01/compile_lane.py RiffleLowerV2.Model.FiniteLaws
LB01 BUILD_OK

$ python3 audit/LB01/compile_lane.py RiffleLowerV2.Model.Sorting
LB01 BUILD_OK
```

The wrapper serializes the frozen lane builder and writes only the LB-01 overlay, using the pinned Lean 4.33.1 runtime and frozen mathlib/dependency checks. The complete lane's axiom-closure/export inventory remains the coordinator's final audit responsibility; this handoff does not claim that the whole graph or physical endpoint follows from these five exports alone.

The finite-law build was rerun successfully after adding `columnMarginal`; the recorded finite-law source hash is for that final checked version.

## Independent physical-construction read

At the physical implementer's request, the reviewer read the new `physicalColumnShear`, `physicalPullback`, `physicalInverseList`, `sort_cons`, and `stableSort_physicalPullback` draft independently. The fold-right inverse formula is `tailInverse ∘ sort(head)`, matching inversion of the frozen chronological forward fold. Recursion changes only tail columns; the subsequent head shear pulls current-position digits through the inverse sorted-tail deck. The pointwise theorem compares stable sort of the transformed sample with physical inverse of the original sample. Earlier columns remain primary and complete ties retain original label order. No chronology or stronger-pointwise-identity defect was found. Kernel verification of that separate source belongs to its implementer and the final lane build.
