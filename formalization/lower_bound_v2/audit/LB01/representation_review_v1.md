# LB-01 independent representation and orientation review, v1

Date: 2026-10-01. Reviewer: independent `representation_review` worker.

This is a pre-proof review of the frozen v1 definitions and intended exports. It does not certify any new Lean theorem. Only this report was written; no shared definition, target, original package, manuscript, build configuration, or old audit was changed. The mathematical-paper skill's writing profile and audit checklist were applied.

## Verdict

The frozen representation matches `lem:ub-graph-representation`. The stable-sort, path-component, and physical permutation orientations are compatible. No extra positivity or nondegeneracy assumptions are needed for the finite law identities. In particular, the statements may retain all natural `k`, `N`, and `K` permitted by `Cuts`.

One tempting stronger statement is false: `physicalInverse ω = stableSort ω` does not hold samplewise. The frozen target correctly asks only for equality of laws. A triangular, measure-preserving relabelling of the columns is required before a deterministic equality can be proved. The existing definitional inversion adapter supplies none of that missing argument.

The release `audit/LB00/CONTRACT_READY.md` was read. It explicitly releases concrete definitions and routine adapters, while recording all LB-01 law identifications as pending. The exact targets were inspected in `Contracts/v1/ModelThinning.lean` and `Contracts/v1/AdditionalFinite.lean`; a proposition naming a target has not been treated as a proof.

## Source and API evidence

Inspected source:

- Manuscript definitions near lines 88–110 and graph representation statement/proof near lines 403–445.
- `RiffleLowerV2/Shared/Model.lean`, `Path.lean`, `Adapters.lean`, and `Smoke.lean`.
- Canonical `formalization/time_profile/RiffleTimeProfile/FixedCountModel.lean`, with the reindexing/factorization interfaces in `FixedCountMoments.lean`.
- Canonical `formalization/foundations/RiffleShuffle/Basic.lean`, `Words.lean`, `Matrices.lean`, and `Graphs.lean`.
- Old `lean-lower-bound/RiffleLower/FixedColumns.lean`, `Sorting.lean`, and `LowerBounds.lean`.
- The pinned local source `formalization/.lake/packages/mathlib/Mathlib/Data/Fin/Tuple/Sort.lean`.

The canonical word type is a list vector, ordered by the inherited lexicographic order on its underlying list. Earlier list positions therefore take priority. The old lower package uses `Lex (Fin K → Fin k)`; this is a different type/order presentation and cannot be identified with the vector order by notation alone. Reuse of its old shuffle law would require both an order adapter and an actual pushforward equivalence between its permutation-valued sample space and the canonical uniform-assignment sample space.

The pinned `Tuple.sort` constructs the ordered list of `(value, originalIndex)` pairs. Its function maps **sorted position to original index**. The exact useful characterization is:

```lean
Tuple.eq_sort_iff :
  σ = Tuple.sort f ↔
    Monotone (f ∘ σ) ∧
    ∀ i j, i < j → f (σ i) = f (σ j) → σ i < σ j
```

Thus `Tuple.monotone_sort` alone establishes sorted keys, while `eq_sort_iff` supplies the essential tie-order condition and uniqueness of the stable sorting permutation. `Tuple.comp_perm_comp_sort_eq_comp_sort` identifies sorted **key tuples**, not sorting permutations.

The old `Sorting.lean` has one positional call to `Tuple.lt_card_le_iff_apply_le_of_monotone` that must be adapted if ported: in the pinned version `f`, `a`, and `j` are implicit. The foundations file already uses the compatible API. This is a proof-only API issue, not a mathematical gap.

## Stable sorting, ranks, and graph components

`stableSort ω := Tuple.sort (rowWord ω)` has the intended position-to-label convention. `sortedWord ω i` evaluates the original row at that returned label. Equal sorted words retain increasing original labels, exactly as required by the inverse-shuffle interpretation.

`lowerRank` and `upperRank` count original rows whose truncations are respectively below or at most the given prefix. Reindexing by `stableSort` preserves both counts. Monotonicity of truncation, supplied by canonical `take_lex_monotone`, then gives the exact interval `[lowerRank, upperRank)` on zero-based positions. The already proved `rank_interval_iff` converts this to the manuscript's `(L,U]` convention. No prefix-legality premise is needed: unrealized prefixes give an empty interval. The empty prefix gives the entire deck, including the empty-deck case.

`shuffleEdges` contains precisely the adjacent positions whose full words coincide. Monotonicity makes every equal-word class an interval. Accordingly, `componentIndex` is constant exactly on full-word classes for a generated graph. It is an increasing enumeration of path components for an arbitrary path-edge set; absent edges increment the component number. Canonical `reachable_iff_eq` verifies the same component identification for the foundational `SimpleGraph` representation, and `matrix_graph_adapter` checks its adjacent-edge interface under the foundational type's `0 < N` and `2 ≤ k` premises. Those premises belong to that adapter's `PileProfile` constructor, not to the actual LB-01 finite law claims.

`componentSort G π` first sorts position indices by `(componentIndex G i, π i)` and then applies `π`. Because component indices are monotone, the sorted indices remain in their original component intervals. Hence it preserves each component's set of values and arranges those values increasingly. The use of `.trans π` has the correct orientation: its value at `i` is `π (sortKey i)`.

Recommended exact deterministic helper interfaces, all provable in the owned model subtree without shared changes:

```lean
theorem componentIndex_monotone {N : ℕ} (G : PathEdges N) :
    Monotone (componentIndex G)

theorem generated_component_iff {k N K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (ω : Sample cuts) (i j : Fin N) :
    componentIndex (shuffleEdges ω) i = componentIndex (shuffleEdges ω) j ↔
      sortedWord ω i = sortedWord ω j

theorem component_sort_preserves_component {N : ℕ}
    (G : PathEdges N) (π : Permutation N) (i : Fin N) :
    componentIndex G
      (Tuple.sort (fun j => (toLex (componentIndex G j, π j) : ℕ ×ₗ Fin N)) i) =
      componentIndex G i

theorem componentSort_increasing {N : ℕ} (G : PathEdges N)
    (π : Permutation N) (i j : Fin N) (hij : i < j)
    (hc : componentIndex G i = componentIndex G j) :
    componentSort G π i < componentSort G π j
```

These names are proposals, not declarations claimed to exist.

## A concrete orbit identity for the graph proof

Let `relabel σ ω` be the sample with row `i` equal to the old row `σ i`; it is an actual sample equivalence, using the same `σ` in every column. Then the following pointwise identity is correctly oriented:

```lean
stableSort (relabel σ ω) =
  componentSort (shuffleEdges ω) ((stableSort ω).trans σ.symm)
```

Indeed the provisional labels at ordered word positions are `σ.symm (stableSort ω i)`, and `componentSort` puts precisely these labels into increasing order within equal-word blocks. The sorted full-word tuple is unchanged by row relabelling. Its monotonicity and the component tie property establish the displayed equality via `Tuple.eq_sort_iff`.

For a fixed sample `ω`, the map `σ ↦ (stableSort ω).trans σ.symm` is a bijection of the permutation group. Averaging the identity over an independent uniform `σ`, and then using uniform row-relabel invariance of the sample, gives the unconditional graph law identity. This avoids adding a conditional-law assumption or a separate notion of conditioning. It also gives the uniform label-set interpretation on every positive-probability multiset atom.

The assignment explicitly also requests equal fiber sizes. That count can be recorded separately: if an output permutation is increasing on the components of `G`, its fiber under `componentSort G` has cardinality `∏ C, (card C)!`; otherwise the fiber is empty. Each fiber consists of independent within-component reorderings. The orbit-average law proof must not be described as a checked Lean factorial count until that separate assertion has actually been proved.

## Physical chronology and the required triangular transformation

Write `S_j = Tuple.sort ((ω j).val)` and `τ_j = S_j.symm`. `oneStepForward` correctly uses `τ_j`: a sorted list of an interleaving's digit word lists the original pile positions, whereas its inverse sends each output position to its original pre-interleaving position. For a deck represented as position-to-label, the update is `D ∘ τ_j`, represented in Lean by `τ_j.trans D`.

Consequently, at two steps the frozen definitions give

```text
physicalForward = τ₀ ∘ τ₁
physicalInverse = S₁ ∘ S₀.
```

The inverse process therefore executes the stable sort for time 1 first and for time 0 second. This is compatible with earlier-column lexicographic priority once each current-position assignment is pulled back to original labels.

For general `K`, define `D_j = S_(K-1) ∘ ... ∘ S_(j+1)`, the inverse-process deck immediately before step `j`, with an empty composition equal to the identity. Define transformed column assignments by

```text
T(ω)_j(i) = (ω j).val (D_j.symm i).
```

Each transformed column has the original prescribed counts. Its defining permutation depends only on the original columns with index strictly greater than `j`.

A reverse-time induction proves

```lean
stableSort (T ω) = physicalInverse ω
```

by stable radix sorting. The generic two-key helper has the precise orientation

```lean
Tuple.sort (fun i => (toLex (f i, g i) : α ×ₗ β)) =
  (Tuple.sort (fun i => f (Tuple.sort g i))).trans (Tuple.sort g)
```

for linearly ordered `α` and `β`; ties in both keys preserve original labels. The full-word variant must establish that the chronological `List.Vector.ofFn` order agrees with this earlier-key priority. It cannot silently reverse the word coordinates.

There are two concrete ways to prove the law-preserving part:

1. Give the triangular map an explicit inverse, recovering original columns in descending index order.
2. Realize it as a composition of coordinate shears in ascending index order. A shear changes column `j` by `D_j.symm`; its inverse changes that column by `D_j`. Updating column `j` does not alter `D_j`, since `D_j` uses only later columns. In ascending order the future columns are still raw when the shear is applied. Each shear is an equivalence of the canonical sample space, so its composition preserves the uniform PMF.

The second route is a useful implementation plan because it reduces measure preservation to finite equivalence invariance and requires no conditional probability API. Both routes use local helper definitions only. Needed interfaces are a column-reindex equivalence, uniform PMF invariance under an equivalence, finite-list composition/reversal identities, and the stable-radix helper. No changes to the frozen physical definitions or targets are recommended.

After these facts, pushforward composition gives `physicalInverseLaw cuts = matrixLaw cuts`. The existing `physicalInverseLaw_eq_map` only proves inversion of the forward law; it must remain explicitly separate from this new physical/matrix bridge.

## Counterexample and finite checks

The false samplewise identity has the smallest transparent witness `N=2`, `k=2`, `K=2`, with both column profiles `(1,1)` and columns

```text
time 0: (0,1)
time 1: (1,0).
```

The original row words are `(0,1)` and `(1,0)`, so their full-word stable sort is the identity. The first one-step sorting permutation is the identity and the second is the transposition, so `physicalInverse` is the transposition. The transformation above changes time-0's assignment to `(1,0)`, and the transformed full-word sort is then the transposition as required.

A direct, exact-integer Python enumeration was run from the inspected definitions, not via floating point probabilities:

- For every binary-column matrix with `0 ≤ N ≤ 4` and `0 ≤ K ≤ 3`, grouped by its complete sequence of fixed column counts, the matrix and physical-inverse output histograms were equal.
- For each such fixed-count profile, `N!` times the matrix-output histogram equalled the sum, over matrices and all uniform-permutation outcomes, of the component-sort output histogram.
- This covered 20 `(N,K)` pairs, 300 fixed-count profiles, and 5,058 matrix samples.
- For every path-edge subset and permutation with `0 ≤ N ≤ 5`, component sorting preserved the component's value set and was strictly increasing along every present edge: 2,142 checks.

These checks include `K=0`, empty and one-card decks, equal words, all-singleton graphs, a single giant component, deterministic columns, and zero piles. They are diagnostic evidence only, not Lean proofs. In particular, at `K=0` all words coincide, the graph is the full path when applicable, both physical and matrix outputs are the identity, and sorting a uniform permutation on that one component also gives the identity. An empty graph gives `componentSort G π = π`; a full path gives the identity. No edge case exposed a missing hypothesis.

## Export and completion ledger

The proposed completed public declarations retain exactly the frozen interfaces:

```lean
RiffleLowerV2.Model.columnIndependence : RiffleLowerV2.Targets.ColumnIndependence
RiffleLowerV2.Model.rowRelabeling : RiffleLowerV2.Targets.RowRelabeling
RiffleLowerV2.Model.stableTie : RiffleLowerV2.Targets.StableTie
RiffleLowerV2.Model.prefixRanks : RiffleLowerV2.Targets.PrefixRanks
RiffleLowerV2.Model.graphRepresentation : RiffleLowerV2.Targets.GraphRepresentation
RiffleLowerV2.Model.graphEventIdentity : RiffleLowerV2.Targets.GraphEventIdentity
RiffleLowerV2.Model.physicalMatrixBridge : RiffleLowerV2.Targets.PhysicalMatrixBridge
RiffleLowerV2.Model.inversionTV : RiffleLowerV2.Targets.InversionTV
```

Their status remains pending in this pre-proof report. The stable-tie and prefix-rank interfaces are supported by already inspected trusted sorting/counting facts; the graph law requires the actual relabelling/orbit argument; the physical law requires the actual triangular transformation. Inversion TV follows from the bijection `Equiv.symm` and invariance of uniform permutation law, with no relation to a particular shuffle needed.

No additional shared assumption, weakened conclusion, or target version change is requested. Proofs may begin only under the coordinator's reviewed proposal/receipt procedure. This report itself provides no Lean build log or new axiom closure because no proof implementation was authorized for this review phase.
