# COMPLETED_INPUT — LB-01 / v1

Released 2026-10-01T15:37:48.909150+00:00.

**LB-01 is complete, including the chronological physical-law bridge.** All eight frozen theorem targets are proved. The full source graph representation is exported for the actual physical inverse shuffle, with a genuinely independent uniform permutation. No LB-01 proof obligation remains pending.

## Downstream use

```lean
import RiffleLowerV2.Model.Main
```

`RiffleLowerV2.Model.physical_graph_event` is the direct physical-law event interface:

```lean
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K)
    (A : RiffleLowerV2.Permutation N → Prop),
  RiffleLowerV2.probability (RiffleLowerV2.physicalInverseLaw cuts) A =
    RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) (fun ω =>
      RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) (fun π =>
        A (RiffleLowerV2.componentSort (RiffleLowerV2.shuffleEdges ω) π)))
```

The required exact export names/types are:

| Declaration under `RiffleLowerV2.Model` | Frozen type under `RiffleLowerV2.Targets` |
|---|---|
| `columnIndependence` | `ColumnIndependence` |
| `rowRelabeling` | `RowRelabeling` |
| `stableTie` | `StableTie` |
| `prefixRanks` | `PrefixRanks` |
| `graphRepresentation` | `GraphRepresentation` |
| `graphEventIdentity` | `GraphEventIdentity` |
| `physicalMatrixBridge` | `PhysicalMatrixBridge` |
| `inversionTV` | `InversionTV` |

[EXPORTS_v1.md](EXPORTS_v1.md) gives every exact compiled public type. [DEPENDENCY_LEDGER_v1.md](DEPENDENCY_LEDGER_v1.md) maps the source paragraphs to checked declarations and records every obligation as proved. The machine-readable receipt is [COMPLETED_INPUT_v1.json](COMPLETED_INPUT_v1.json).

## What was proved

The canonical dependent sample has independent uniform columns (`columnIndependence` and `columnMarginal`), and its law is invariant under explicit row-relabel equivalences. Stable ties, exact prefix rank intervals and component/word-block equivalence are checked on the shared representations.

`matrix_multiset_expect` and `matrix_multiset_event` provide the full-multiset conditional law as unconditional finite identities, valid even on impossible atoms. `sampleRelabel_fiber_card` counts canonical assignment fibers. `shuffle_componentSort_fiber_card_eq` gives the product of component factorials for every supported output and zero for every unsupported output. Products over absent words contribute only `0!=1`.

`physicalPullbackEquiv` is an actual triangular bijection of canonical fixed-count samples. Its deterministic sorting identity proves reverse chronological inversion and earlier-column lexicographic priority. Uniform invariance then proves `physicalMatrixBridge`. This does not assert the false identity between physical inversion and matrix sorting on the same raw sample.

All statements retain the frozen quantifiers over arbitrary natural k,N,K and every Cuts value. Empty decks/times, zero piles and deterministic columns are covered. No threshold, asymptotic constant, positivity restriction or hidden graph-law premise was added.

## Verification

From `formalization/lower_bound_v2`:

```text
python3 audit/LB01/compile_lane.py RiffleLowerV2.Model.Main
# delegates to: python3 scripts/lane.py LB01 RiffleLowerV2.Model.Main
LB01 BUILD_OK
```

The final combined lane build succeeded with exit 0; see [lane-build-v1.log](lane-build-v1.log). It recompiles every imported owned module in `.build/lanes/LB01/lib/lean`, using Lean 4.33.1 and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

`audit/LB01/Check.lean` separately compiled with warnings treated as errors. It verifies assignments to all eight frozen target types and inspects the transitive axiom closure of all **162** new elaborated declarations, including generated/private helpers. The union is exactly **propext, Classical.choice, Quot.sound**. No custom axiom, proof placeholder or native proof oracle enters the checked closure. See [VERIFICATION_v1.json](VERIFICATION_v1.json) and [compiled-audit-v1.log](compiled-audit-v1.log).

Independent pre-proof mathematical, representation and counterexample reviews agreed on the frozen statements. The final independent review passed on the final source hashes; the physical implementation was reviewed by a different worker and the lane owner. All findings are resolved. Exact finite sanity checks additionally covered 33,300 matrices, 1,775 fixed-count profiles, 5,078 complete-multiset fibers and 2,142 graph/permutation pairs; those checks are not used as formal proof.

## Provenance and integration boundary

Authoritative manuscript SHA-256: `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`.

Frozen LB-00 v1 manifest SHA-256: `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`.

All bound shared files and original source hashes were rechecked unchanged. Input authorization is the released `audit/LB00/CONTRACT_READY.md` plus `audit/LB00/LB01_INTERFACE_ACK_v1.md`. Only owned Model/ and audit/LB01/ source paths were written, with generated build output confined to the assigned lane area. Legacy finite-law/sorting proof patterns and old/new hashes are documented; no legacy permutation sample space or unchecked cache is imported.

The coordinator may compile `RiffleLowerV2.Model.Main` into its integration overlay for downstream lanes. This requires no frozen-source edit or contract change. The lower-bound endpoints E and M belong to other lanes and are not claimed by this receipt.
