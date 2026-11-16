# LB-01 final independent representation review, v1

Date: 2026-10-01. Reviewer: `representation_review` worker.

**Verdict: pass for the reviewed source.** The implemented statements match the frozen LB-01 obligations. The graph-mixture proof uses the actual canonical sample law and the independently sampled uniform permutation. The full-multiset identity and both sample-relabel and component-sort factorial fibers are proved, rather than assumed. No substantive mathematical or representation issue remains in the files reviewed here.

This is an independent source review of other authors' files. The reviewer authored `Physical.lean` and therefore does not count this report as independent review of that module. The physical module has separate independent review; this report checks only that `Main.lean` composes its exact exported theorem with the graph theorem correctly. No proof source was edited during this final review. The final file hashes were taken after the lane owner explicitly declared the proof sources stable and after the intended `ComponentFibers` import was present in `Main`.

## Reviewed source identity

Paths below are relative to `formalization/lower_bound_v2`.

| Source | SHA-256 |
| --- | --- |
| `RiffleLowerV2/Model/FiniteLaws.lean` | `cc5abe4ecf21f682658ca77e7a867368a4f1f8c4ab0b9d70eba79a9041772a06` |
| `RiffleLowerV2/Model/Sorting.lean` | `ab2e2fd9f105ab4fac52f6764d731aad7a93a34f5cb6cd85660b67eacd595a54` |
| `RiffleLowerV2/Model/GraphSorting.lean` | `66201c1a8aa75da4d0fd5855ab251d3cded0e3fb90e5df734c6c95862be880f0` |
| `RiffleLowerV2/Model/GraphLaw.lean` | `9a15859e7f7b9be119b534ff177f4ce65d75ac88df779148c8cbaa27935a7103` |
| `RiffleLowerV2/Model/FiberCounts.lean` | `a047c4cda586bacc6c19fec75e9a4905097860fa7f075917bcb213c7d6aad349` |
| `RiffleLowerV2/Model/ComponentFibers.lean` | `ca0b61143fb2aaa5ac68a868185449d4c5ef2b3800cbad971e041b01ecdd482a` |
| `RiffleLowerV2/Model/Main.lean` | `3300883af41f03098138ce53c49eb5a547cb7c247448cd8ee32abc0d838a0822` |

The mathematical source is `lem:ub-graph-representation` and its surrounding matrix/graph definitions in the unchanged manuscript. Exact target definitions were compared in `Contracts/v1/ModelThinning.lean` and `Contracts/v1/AdditionalFinite.lean`, together with the concrete shared definitions. This report uses the original LB-00 readiness receipt and its additive `LB01_INTERFACE_ACK_v1.md`; it does not revise either contract.

## Exact frozen obligations

All declarations in this table have the namespace prefix `RiffleLowerV2.Model`.

| Declaration | Exact frozen type | Review result |
| --- | --- | --- |
| `columnIndependence` | `Targets.ColumnIndependence` | Proves the dependent-product expectation identity on the actual fixed-count PMF. |
| `rowRelabeling` | `Targets.RowRelabeling` | Proves the required `sampleRow` pushforward equality via an actual sample equivalence. |
| `stableTie` | `Targets.StableTie` | Uses the actual `Tuple.sort` tie clause; sorted positions map to increasing original labels within full-word ties. |
| `prefixRanks` | `Targets.PrefixRanks` | Gives both the exact half-open zero-based interval and its cardinality. |
| `graphRepresentation` | `Targets.GraphRepresentation` | Identifies the concrete matrix law with the frozen independent graph mixture. |
| `graphEventIdentity` | `Targets.GraphEventIdentity` | Provides the exact event interface, derived from the proved PMF identity. |
| `inversionTV` | `Targets.InversionTV` | Preserves the frozen half-L1 TV normalization under inversion against uniform law. |

`physicalMatrixBridge : Targets.PhysicalMatrixBridge` is imported from the separately reviewed physical module. `Main.physical_graph_representation` composes this theorem with `graphRepresentation` in the correct direction, and `physical_graph_event` transfers the exact event formula to `physicalInverseLaw`. There is no physical/matrix equality premise in either endpoint.

All frozen natural-number domains remain unchanged. No positive-deck, positive-pile, alphabet-size, graph-regularity, or conditional-independence premise was added. Empty decks/times and zero piles remain within the theorem types.

## Finite probability and canonical row relabelling

`FiniteLaws` works directly with the canonical uniform `TimeProfile.ColumnAssignments` and dependent-product `ShuffleSample`. It does not identify the old permutation-column sample space with this space or import the old real-valued finite-law implementation.

The expectation calculations account for `ENNReal.toReal` explicitly. Finite PMF masses are finite, which is used when recovering PMF equality from equality of all real singleton expectations. `columnIndependence` specializes finite product-sum factorization to the exact sample type. `columnMarginal` additionally proves that every coordinate pushforward is the declared uniform `columnPMF`; uniformity is not inferred merely from an informal description of the sample.

`columnEquiv` precomposes assignments by a label permutation and proves histogram preservation. Its inverse precomposes by the inverse permutation. `sampleRelabel` applies this to every column, and `map_uniform_equiv` proves sample-law preservation. The target `rowRelabeling` follows by mapping that already proved sample-law equality to rows. No exchangeability or independence assumption is inserted into a structure field.

`inversionTV` reindexes the actual finite L1 sum through the inversion equivalence. Since every uniform mass is the same, this preserves the reference term as well as the nonuniform law, and the outer division by two is unchanged.

## Stable sorting, prefix ranks, and generated components

`stableTie` invokes the stable sorting characterization, not only monotonicity. `prefixRanks` reindexes the raw prefix comparisons through `stableSort`, uses monotonicity of list truncation, and proves the count formula by the difference of the nested lower/upper sets. This handles absent prefixes and empty realized intervals without a legality assumption. There is no mismatch between full-word order and truncated-word comparison.

The additional review of `GraphSorting` verifies the deterministic representation on which `GraphLaw` depends. Component indices are monotone for any path-edge set. For a monotone key tuple, equality of component indices is proved equivalent to equality of keys. The converse direction is proved by traversing adjacent positions, so no connectivity premise has been omitted. Specializing to `sortedWord` gives `shuffle_componentIndex_eq_iff` and identifies exactly the actual `shuffleEdges` components.

Sorting `(componentIndex, label)` preserves the already sorted first coordinate and strictly increases the second coordinate inside each component. Therefore the frozen `componentSort` both keeps the assigned label set in its component and sorts it increasingly. The pointwise relabelling identity has the checked orientation

```lean
stableSort (sampleRelabel cuts ρ ω) =
  componentSort (shuffleEdges ω) ((stableSort ω).trans ρ.symm)
```

The right-hand provisional label at position `i` is `ρ.symm (stableSort ω i)`, as required for row precomposition by `ρ`. Its proof uses both sorted-key monotonicity and the stable-tie condition. `sortedWord_relabel` proves equality of the complete sorted key tuple; it does not incorrectly equate sorting permutations under relabelling.

## Full-multiset identity and genuine independent sampling

`matrix_multiset_expect` proves the following identity for **every** real-valued test `F` of the entire sorted word tuple and output permutation:

```text
Eω F(sortedWord ω, stableSort ω)
  = Eω Eπ F(sortedWord ω, componentSort(shuffleEdges ω, π)).
```

The sorted tuple is a canonical encoding of the full word multiset, including every multiplicity. Consequently this is a joint law identity on full multisets, not merely an identity after conditioning on the coarser graph. The proof averages over uniform row relabellings, uses exact sample-law invariance and invariance of the sorted tuple, swaps two finite expectations, and applies the proved deterministic relabelling identity. For each fixed `ω`, `relabelToLabels (stableSort ω)` is an explicit permutation-group equivalence; it turns the inner uniform relabelling into an inner uniform label permutation.

The resulting law is exactly the frozen construction

```lean
(fixedCountPMF cuts).bind fun ω =>
  (uniformPermutation N).map (componentSort (shuffleEdges ω))
```

Thus `π` is sampled independently after `ω`. A permutation that is only marginally uniform has not been substituted for this construction. Although the change of variables used to prove the identity depends on the fixed outer sample, it preserves the uniform inner law separately for every outer sample, which is precisely what the displayed bind requires.

`matrix_multiset_event` explicitly specializes the joint identity to the intersection of a complete multiset atom and an output event. It uses no division and remains valid for impossible atoms. Dividing both sides by the atom's positive probability yields the ordinary conditional statement; no assertion is made about conditioning on a zero-probability atom. This is the equivalent unconditional finite identity authorized by the assignment.

## Exact factorial fibers

`FiberCounts` constructs an equivalence from the key stabilizer to the product of permutation groups of all key fibers. The cardinality is therefore the product of the fiber factorials. The trusted `Equiv.ofFiberEquiv` used here was checked in the pinned mathlib source: it assembles equivalences of actual fibers into an equivalence of the full domain, and its map theorem preserves the key.

For a realized key assignment, `keyAssignmentFiberEquiv` translates its fiber to the stabilizer using an explicit realizing permutation. This witness is only a nonemptiness witness, and its concrete specialization is discharged. `exists_relabel_of_sortedWord_eq` constructs that realizing permutation from the two stable sorting permutations. `sample_eq_iff_rowWord` proves that equality of full rows determines equality of the actual dependent column sample. Thus `sampleRelabel_fiber_card` is an actual canonical-sample fiber count, not an abstract count left behind an undispatched model-equivalence hypothesis.

`ComponentFibers` counts the literal preimage under the frozen `componentSort`. Its `BlockIncreasing` premise is exactly the necessary support condition, and the negated case is handled separately. For generated graphs, the complete total formula is

```text
card {π | componentSort (shuffleEdges ω) π = σ}
  = if BlockIncreasing (shuffleEdges ω) σ
    then ∏ w, (card {i | sortedWord ω i = w})!
    else 0.
```

`shuffleComponentFiberEquiv` connects this literal preimage to the already counted full-word assignment fiber, with inversion in both directions. The specialization supplies `σ.symm` as the realizing assignment. Each realized word class is one graph component; unrealized words contribute `0! = 1`. Hence this is exactly the manuscript's product of component factorials. The empty-deck and single-component extremes remain valid.

The graph law itself is proved by the orbit-average identity, while the factorial count is proved independently. The separation is mathematically valid and does not leave the requested count unproved. `Main` now imports `ComponentFibers`, which also imports `FiberCounts`, so the complete proof entry point makes both counting layers available.

## Assumptions, verification limits, and resolution

A source scan of the model subtree found no explicit proof placeholders, custom axioms, native proof oracle, or unsafe declaration. None of the new theorem signatures assumes a desired graph or physical law, and no required specialization remains conditional on a generic model interface. The only helper premises express ordinary finite structure or the necessary supported-fiber condition, and the concrete uses discharge them.

The lane owner reported successful individual compilation of every reviewed proof file and was running the combined `Main` build when this report was finalized. This worker did not duplicate those builds or claim an independently executed kernel audit. The final combined build log and exact transitive axiom closure belong to the lane verification record and must accompany the completed-input receipt. This source review is not a substitute for either.

The sole integration observation during review was that the initial `Main` snapshot had not yet imported `ComponentFibers`. The intended import was added before the stable snapshot and was verified above. It is resolved. No remaining revision request, mathematical caveat, or shared-contract change is identified by this review.
