# LB02 final compatibility provenance review

Date: 2026-10-01. This verification recomputed hashes from the current filesystem and read the final full-lane declaration/closure output. No proof source, original source, initial snapshot, receipt, or old audit was changed; this report is the only new file created by this pass. No new build was run in this review.

## Verdict and governing records

All seven current compatibility ports exactly match the final hashes in `compat_receipt_v1.json`. All seven original `lean/Shuffle/` files exactly match their original hashes in both `compat_provenance_v1.json` and `compat_receipt_v1.json`. The current new helper/audit files recorded in the final compatibility receipt also match, as do the three source hashes in `compat_sampling_receipt_v1.json`.

`compat_provenance_v1.json` is a preserved development snapshot, created before the last compatibility fixes. Its original-source hashes remain valid; its port hashes are not the final port certificate. `compat_receipt_v1.json`, associated with the successful `compat_build_v6.log`, governs the final seven compatibility ports. `compat_sampling_receipt_v1.json`, associated with successful `compat_column_build_v2.log`, separately governs the later concrete permutation/column bridges.

Exactly three current port hashes differ from the earlier snapshot: `Conditioning.lean`, `SubsetSampling.lean`, and `HypergeometricConcentration.lean`. These are the expected checked compatibility fixes, documented in the final receipt and component report. The other four initial port hashes already equal their final hashes. There is no unexplained hash discrepancy and no reason to rewrite the initial provenance snapshot to make it appear final.

## Recomputed source hashes

Each original below is in workspace `lean/Shuffle/`; each port is in `formalization/lower_bound_v2/RiffleLowerV2/Thinning/Compat/`.

| File | Original SHA-256, unchanged | Current port SHA-256, matching final receipt |
| --- | --- | --- |
| `FiniteLaw.lean` | `f5dcbcfa6908503696d6edaa363a8a0919a22aabd8e01e9819e6f13d20baff17` | `0aea699fe721acd93eb38772b280630b822dfa31495349baf55877110cd9d182` |
| `Conditioning.lean` | `d38948fc44f5a107aa3aff794ffd20db7f87d901bc8c104eff4486e9937730b4` | `59f90c6082c35defc4cb107e9ff16365bfd5d1dd849e573c4406b57332445403` |
| `Hypergeometric.lean` | `dd55c562c7b52821bbc06412786d1a2a98df0b9be97a41b6b0a4924254cb0809` | `60ddfc6791ce509faac5cbebd3461406eb80f5b515e383499d86a5884f09655b` |
| `HypergeometricMoments.lean` | `c667d6024b8e6aadf26c917e4bc97dbc13f5efb570af0edfbecef4283117b109` | `683abd2e64966bb8dfd229b9f7d0ab93bb2c68a446f2f5ee1d0fbbaa47615ce0` |
| `SubsetSampling.lean` | `23da7cc182126632e7f5f0f0e897f9da15bd06aa17247023a9722ccd74d86042` | `f1f1966a32a32f77786c334424dc264c2f25cc8f407984766ebb4bdfa7306629` |
| `ResidualSampling.lean` | `30c78cd52fd8ee7ea88f12fb2123d093573d6d4434c192a93a486df810f64d04` | `76adf5628deddc7f8f4c2e1eb141401599013e8158b321d8e2687da67b5809d8` |
| `HypergeometricConcentration.lean` | `156d6e9aa774c2e3498975acfb64d9622dfc6d923cfcd96db5a866c4592e5a14` | `88d1a5b1dcaa900583ea8f7871d540af93a419a111dcb18787c3a177859d1915` |

The later changes in Conditioning supply existing positive-event proofs explicitly and reconcile different decision procedures in the same finite rectangle identity. SubsetSampling explicitly reduces a pair-map application and uses the pinned `card_sdiff_of_subset` name. HypergeometricConcentration fixes field simplification and explicitly aligns the Fin summation domains/reverse values before rewriting. These preserve the retained mathematical statements; the new all-s theorem has its separately recorded stronger signature.

## Final full-build all-s bridge and closure

I inspected `RiffleLowerV2/Thinning/Check.lean` and parsed all 472 unique `LB02_DECLARATION_JSON` records in `final_build_and_axioms_v1.log`. The log ends with `LB02 BUILD_OK`. The audit code checks the exact seven frozen target types and rejects every collected dependency outside `propext`, `Classical.choice`, and `Quot.sound`. The union over the actual 472 records is exactly those three standard axioms.

The following entries are actual theorem declarations in the final build, each with only that standard closure:

- `RiffleLowerV2.Thinning.Compat.HypergeomParams.expect_pow_le_all`: every s>0; no s≤1 premise. Its proof dependencies include both the retained s≤1 theorem and the proved private positive-u helper.
- `RiffleLowerV2.Thinning.Compat.sample_expect_intersection_eq_hypergeom`: arbitrary test functions under the actual uniform subset law; proof dependencies include `sample_intersection_law` and `FiniteLaw.expect_eq_of_count_law`.
- `RiffleLowerV2.Thinning.Compat.sample_expect_pow_intersection_le`: the all-s transform for any fixed A⊆V under the actual `sampleLaw`, using the preceding expectation bridge and `expect_pow_le_all`.
- `RiffleLowerV2.Thinning.permutation_subset_expect` and `permutation_intersection_transform`: the concrete uniform-permutation bridge and arbitrary deterministic marked-set transform.
- `RiffleLowerV2.Thinning.hypergeometricTransform`: exact type `RiffleLowerV2.Targets.HypergeometricTransform`, with no additional theorem premise.
- `RiffleLowerV2.Thinning.column_subset_expect` and `column_intersection_transform`: actual shared fixed-histogram column law, uniformly over arbitrary marked A and every s>0.
- `RiffleLowerV2.Thinning.prefixTransform` and `successiveThinning`: concrete prefix and permutation-product conclusions using the above bridges and proved backward affine recursion.

The final elaborated proof dependency graph contains these paths, which were checked from `value_dependencies` rather than inferred from filenames:

```text
hypergeometricTransform
  → permutation_intersection_transform
  → Compat.sample_expect_pow_intersection_le
  → Compat.HypergeomParams.expect_pow_le_all

prefixTransform
  → column_intersection_transform
  → Compat.sample_expect_pow_intersection_le
  → Compat.HypergeomParams.expect_pow_le_all
```

Thus the concrete all-s bridge is present in the final full build and is used by the concrete prefix theorem. The implementation does not merely cite the old public s≤1 lemma as though it were an all-s theorem, and no target predicate is treated as proof evidence.

## Identity of reviewed evidence

| Record | SHA-256 |
| --- | --- |
| `compat_provenance_v1.json` | `4316813a7bd915fedcd2e5d70e470136ffae4af76bd182a7137e74c92dfc795b` |
| `compat_receipt_v1.json` | `0bfe3078cf3c2bd94dcf479a35f65481e572bd042b5f388ea52e3ace0eb0be6a` |
| `compat_sampling_receipt_v1.json` | `9c8cf76e824a3c7ad29d42bf52b4aa30cf8a1a839f3c7d620923b3a4c0f22571` |
| `final_build_and_axioms_v1.log` | `590a42b3a91b2236f1b1269c0c988aa074c1337d82f926032c62e15f82ab4b86` |
| `RiffleLowerV2/Thinning/Check.lean` | `7999d10dfe63199cab05330f7d11a1073a3303da98fd245cc566b9122dc229ea` |

This report resolves the packaging distinction between the preserved initial snapshot and the later successful receipts. It does not alter any historical audit or replace the full-lane delivery ledger.
