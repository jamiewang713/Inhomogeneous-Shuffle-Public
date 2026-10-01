# LB-01 proved-versus-pending ledger, v1

All LB-01 acceptance obligations are proved. The source correspondence is the statement and three proof paragraphs of `lem:ub-graph-representation` in the authoritative manuscript (SHA-256 `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`). This does not prove the lower-bound endpoints assigned to other lanes.

## Exact required exports

All eight are kernel-checked theorem declarations, with exactly the frozen type and unrestricted natural-number parameters. The exact elaborated types of every public helper appear in `EXPORTS_v1.md`; `compiled-declarations-v1.json` records their direct dependencies and axiom closures.

| Export, under `RiffleLowerV2.Model` | Exact type | Status |
|---|---|---|
| `columnIndependence` | `RiffleLowerV2.Targets.ColumnIndependence` | PROVED |
| `rowRelabeling` | `RiffleLowerV2.Targets.RowRelabeling` | PROVED |
| `stableTie` | `RiffleLowerV2.Targets.StableTie` | PROVED |
| `prefixRanks` | `RiffleLowerV2.Targets.PrefixRanks` | PROVED |
| `graphRepresentation` | `RiffleLowerV2.Targets.GraphRepresentation` | PROVED |
| `graphEventIdentity` | `RiffleLowerV2.Targets.GraphEventIdentity` | PROVED |
| `physicalMatrixBridge` | `RiffleLowerV2.Targets.PhysicalMatrixBridge` | PROVED |
| `inversionTV` | `RiffleLowerV2.Targets.InversionTV` | PROVED |

## Concrete obligations and dependency chain

| Obligation | Checked evidence | Dependencies / source correspondence | Status |
|---|---|---|---|
| Canonical columns are individually uniform and independent | `columnMarginal`, `columnIndependence` | Actual `TimeProfile.fixedCountPMF`, `columnPMF`, dependent sample product; paragraph 1 | PROVED |
| Row exchangeability on the actual sample space | `columnEquiv`, `sampleRelabel`, `sampleRelabel_uniform`, `rowRelabeling` | Explicit inverse equivalences preserving fixed counts; paragraphs 1 and 3 | PROVED |
| Stable tie order and sorted-position-to-original-label convention | `stableTie`, `stableSort_relabel` | `Tuple.eq_sort_iff` includes both monotonicity and ties; paragraphs 2 and 3 | PROVED |
| Prefix intervals and exact cardinalities | `prefixRanks`; shared `rank_interval_iff` | Lexicographic truncation, reindexing counts, `[L,U)` equals paper `(L,U]` | PROVED |
| Path components are precisely complete-word blocks | `shuffle_componentIndex_eq_iff`, `shuffle_componentIndex_lt_iff` | Gap-count proof directly for actual `shuffleEdges`, valid without the stricter foundations adapter hypotheses; paragraph 3 | PROVED |
| Component normalization preserves the label set and increases its values | `componentSort_preserves_component`, `componentSort_increasing`, `componentSort_eq_iff` | Frozen lexicographic component/value sort; paragraph 3 | PROVED |
| Uniform assignment conditional on the full-word multiset | `matrix_multiset_expect`, `matrix_multiset_event` | Unconditional identity for arbitrary tests of the entire sorted word array; division is unnecessary, and impossible atoms give zero; paragraph 3 | PROVED |
| Actual assignment fibers have product factorial cardinality | `sampleRelabel_fiber_card` | Explicit equivalences to `KeyAssignmentFiber` and then the product of within-word permutation groups; paragraph 3 | PROVED |
| All actual component-sort fibers have the required count | `shuffle_componentSort_fiber_card_eq` | Product over all full words; absent words contribute `0!=1`; non-block-increasing outputs have zero preimages; paragraph 3 | PROVED |
| Matrix law equals independent graph mixture | `graphRepresentation`, `graphEventIdentity` | Row permutation averaging, finite sum interchange, and the actual frozen nested `bind`/`map` construction; lemma statement for matrix model | PROVED |
| Chronological physical inverse equals matrix law | `physicalPullbackEquiv`, `stableSort_physicalPullback`, `physicalMatrixBridge` | Concrete triangular equivalence; reverse-time fold; stable radix sort with earlier-column priority; paragraphs 1 and 2 | PROVED |
| Full physical graph-law and event endpoint | `physical_graph_representation`, `physical_graph_event` | Proved physical bridge composed with proved concrete graph identity; full lemma statement | PROVED |
| Forward/inverse total variation agreement against uniform | `inversionTV`; shared `physicalInverseLaw_eq_map` | Exact inversion bijection and half-L1 normalization | PROVED |

There are no pending LB-01 mathematical dependencies or hidden law-identification premises. `BlockIncreasing` occurs only in the supported-fiber intermediate theorem; the total fiber theorem and the law endpoints discharge it. All laws and statements use the actual shared objects. No custom axiom, proof placeholder, or native proof oracle occurs in the checked closure.

## Imports and ownership

Downstream import: `RiffleLowerV2.Model.Main`. It imports Sorting, GraphLaw, ComponentFibers and Physical; their imports include FiberCounts, GraphSorting and FiniteLaws. These seven proof modules and one entry module are all within the exclusive `RiffleLowerV2/Model/` tree. The coordinator can register this entry module in its compiled overlay without changing the frozen shared umbrella.

The only upstream lane is LB-00. Its `CONTRACT_READY` v1 and additive `LB01_INTERFACE_ACK_v1.md` were checked before dependent proofs. No other unfinished lane is imported. Old source packages and freezes remain untouched. The implementation never uses the legacy permutation-column sample space, so it requires no unproved identification with the canonical assignment space. The limited legacy proof-pattern reuse and exact old/new signatures/hashes are documented in `finite_sorting_provenance_v1.md`; actual calculations are re-proved directly on the shared PMFs.

## Quantifiers and degenerate cases

Every finite law target retains `∀ {k N K : ℕ}, ∀ cuts : Cuts k N K`. There is no positivity assumption, threshold, asymptotic constant, or extra feasibility condition beyond the shared `Cuts`. The proofs cover `N=0`, `K=0`, zero piles, deterministic columns, equal words, singleton components and a giant component. Inversion TV quantifies over every `N` and every `PMF (Permutation N)`.

The exhaustive diagnostic checker covers 33,300 matrices, 1,775 profiles, 5,078 complete-multiset fibers and 2,142 graph/permutation pairs. It is separate from the general Lean proofs. In particular, the documented raw-sample counterexample remains valid; only the explicitly transformed sample satisfies `stableSort_physicalPullback`.
