# LB09 deterministic rank-barrier delivery v1

`RiffleLowerV2.Localization.RankBarriers` compiled successfully without warnings using:

```text
python3 audit/LB09/serial_build.py RiffleLowerV2.Localization.RankBarriers
LB09 BUILD_OK
```

The compiled output timestamp is later than the final source timestamp. Final source SHA-256: `354cbdde0d9f4a30ddc49f925dae211145369461d33d3cbbeeb71961cd759f75`.

## Exact integration interface

All declarations below are in `RiffleLowerV2.Localization`. The principal result is:

```lean
coldFamily_localized_of_endpoint_reserves
  (cuts : Cuts k N K) (hN : 0 < N)
  (G : ColdGeometryData K P W)
  (hW : W.ms ≤ W.mu) (hK : W.mu + W.bridgeLength ≤ K)
  (hminus : wordOnList G.reserveMinus < wordOnList G.central)
  (hplus : wordOnList G.central < wordOnList G.reservePlus)
  (e : ℝ) (omega : Sample cuts)
  (hbounds : ∀ x ∈ coldPrefixFamily cuts hN P W G,
    |(relativeLowerCount G.ambient W.ms W.mu x omega : ℝ) -
      prefixMean cuts (prefixAt W.ms G.ambient) * relativeMassBefore cuts x| ≤ e ∧
    |(relativeUpperCount G.ambient W.ms W.mu x omega : ℝ) -
      prefixMean cuts (prefixAt W.ms G.ambient) *
        (relativeMassBefore cuts x + massOn cuts x)| ≤ e ∧
    e + 2 ≤ (prefixCount (reservePrefix G x G.reserveMinus) omega : ℝ) ∧
    e + 2 ≤ (prefixCount (reservePrefix G x G.reservePlus) omega : ℝ)) :
  ∀ y ∈ coldFullFamily cuts hN P W G, ∀ i : Fin N,
    sortedWord omega i = y →
    i ∈ clipTranslate N (coldRelativeSet cuts hN P W G)
      (lowerRank (prefixAt W.ms G.ambient) omega : ℤ)
```

Here `k,N,K,P,W` are the implicit parameters specified in the source. This is the deterministic implication consumed by the coordinator's actual simultaneous-prefix event. The endpoint/reserve inequalities are intermediate numerical bounds, not an assumed localization event. The coordinator discharges them using the concrete LB02 concentration theorem and the constructed geometry.

## Proved finite chain

1. `take_eq_map_finRange`, `take_lt_take_iff`, `take_lt_split`, and `take_le_split` prove lexicographic prefix/suffix comparisons directly from first unequal coordinates.
2. `relative_rank_decomposition` proves the exact identities `lowerRank(ax)=q+Lrel` and `upperRank(ax)=q+Urel` by disjoint finite count decompositions.
3. `sorted_take_lt_iff` and `sorted_take_le_iff` reindex actual counts through the stable-sort permutation, using the checked monotone-sorting cardinality theorem. Their proof pattern follows the already checked `Model/Sorting.lean` prefix-rank argument; no sampling independence is involved.
4. `prefixCount_add_lowerRank` uses the actual checked `Model.prefixRanks` equality. `prefix_rank_bounds_of_take_eq` gives rank containment for extensions.
5. `joinColdWord_take_mu_eq` and `joinColdWord_bridge_lt` prove that the bridge order decides comparison before any tail coordinate is read.
6. `coldWord_rank_barriers` proves, for every tail word and every sorted occurrence of the actual joined central word,

   ```text
   q + Lrel + Cminus ≤ i.val,
   i.val + 1 + Cplus ≤ q + Urel.
   ```

7. `coldWord_mem_translate` combines these inequalities with endpoint errors at most `e` and actual reserve counts at least `e+2`. It uses `manuscriptRank i=i.val+1` and the proved half-open integer-membership equivalence. No rank-convention assumption remains.
8. `coldFamily_localized_of_endpoint_reserves` unpacks the actual image-defined full-word family. Its proof uses only the selected prefix membership: the rank-barrier result already covered every tail word on the same sample.

The module neither invokes the target localization predicate as a premise nor selects any event after inspecting a tail word. The word-to-edge injection and probability bound are assembled separately by the coordinator from this proved rank membership.

## Words and bridge provenance addendum

Final source hashes of the preceding worker deliverables are:

| File | SHA-256 |
|---|---|
| `Localization/Words.lean` | `f2ddc788402900b53cbcf979cd7185883502cd69deaab06457407aee7092afa6` |
| `Localization/Bridge.lean` | `2b40a62ac461c103525a152e414a5e92decc5ba7f8a36634a60ad461ac27194b` |
| Read-only `Thinning/MaximalWord.lean` | `fa720aceb1935b1f86926eccfc0a7901177fb945c5b33d2ee8a7bce1b24329b4` |

The fully qualified good-digit helper is `RiffleLowerV2.Localization.goodColumn_ordered_digits`; the earlier Words/Bridge receipt's `Bridge.goodColumn_ordered_digits` was a descriptive file qualification, not a Lean namespace. All actual helper names are defined in the common `Localization` namespace. The coordinator owns the final full-lane axiom-closure and compiled-declaration audit.
