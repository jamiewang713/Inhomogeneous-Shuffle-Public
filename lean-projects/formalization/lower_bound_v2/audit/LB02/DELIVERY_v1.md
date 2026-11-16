# LB02 delivery and import receipt v1

**LB02 is complete against the unchanged frozen v1 targets.** All seven required declarations and the prompt-required concrete specializations compile.

The manuscript, original packages, shared sources, package configuration, umbrella imports, and historical freezes were preserved. This receipt certifies concentration of actual matrix counts; it makes no permutation/run/TV claim.

## Required frozen declarations

| Declaration in `RiffleLowerV2.Thinning` | Exact type | Status |
| --- | --- | --- |
| `successiveThinning` | `RiffleLowerV2.Targets.SuccessiveThinning` | proved |
| `prefixTails` | `RiffleLowerV2.Targets.PrefixTails` | proved |
| `allPrefixConcentration` | `RiffleLowerV2.Targets.AllPrefixConcentration` | proved |
| `prefixFailureUniform` | `RiffleLowerV2.Targets.PrefixFailureUniform` | proved |
| `residualLaw` | `RiffleLowerV2.Targets.ResidualLaw` | proved |
| `hypergeometricTransform` | `RiffleLowerV2.Targets.HypergeometricTransform` | proved |
| `maximalMeanIdentity` | `RiffleLowerV2.Targets.MaximalMeanIdentity` | proved |

`EXPORTS_v1.md` prints the exact compiled types of these and all additional delivery exports. `compiled_declarations_v1.json` records every elaborated lane declaration, its type/body dependencies, and its closure.

## Source correspondence and proof ledger

| Source | Completed obligation | Evidence |
| --- | --- | --- |
| `lem:successive-thinning-tail` | All positive s under the exact uniform-permutation hypergeometric law | `hypergeometricTransform`, `Compat.HypergeomParams.expect_pow_le_all`, `permutation_subset_expect` |
| `lem:successive-thinning-tail` | Independent subset process via exact finite coordinate integration and backward affine recursion | `successiveThinning`, `independent_intersection_transform`, `permutation_intersection_transform` |
| `lem:successive-thinning-tail` | Exact Bernstein, half-mean and fewer-than-two tails; positive population, zero mean and empty columns included | `thinningTails`, `prefixTails`, `chernoffConstant_pos` |
| `lem:successive-thinning-tail` | Actual admissible residual law, subtracted counts, independent residual columns and concrete residual transform/tails | `residualLaw`, `residualColumnIndependence`, `residualPrefixTransform`, `residualPrefixTails` |
| `cor:iterated-hypergeom` | Actual prefix law bridge and explicit simultaneous polynomial union bound over every length | `prefixTransform`, `allPrefixConcentration`, `prefix_card_exact`, `prefix_card_le_of_cuts`, `prefixCount_eq_zero_of_mass_zero` |
| `cor:iterated-hypergeom` | Uniform convergence with k,T,epsilon,delta before N0, then every N,K satisfying K<=T log N | `prefixFailureUniform`, `prefixFailure_le_envelope`, `prefixFailureEnvelope_tendsto` |
| `prop:largest-prefix` | Canonical deterministic maximal word, exact maximal mean/exponent and exponential count tail for LB10 | `maximalMeanIdentity`, `maximalWordTail` |

There are no pending LB02 proof dependencies. LB00 is the sole required upstream lane and its immutable receipt/hash check passed. LB01 law identification and LB10 permutation/run/TV assembly are outside this certificate and are not assumed here. No pending target proposition is used as evidence.

## Verification

Run from `formalization/lower_bound_v2`:

```text
python3 scripts/lane.py LB02 RiffleLowerV2.Thinning.Main
python3 scripts/lane.py LB02 RiffleLowerV2.Thinning.Check
python3 scripts/lane.py LB02 --check-ready
```

`main_build_v2.log` records the successful complete main entry build before the final additive residual-factorization import. `final_build_and_axioms_v1.log` rebuilds the final Main and all transitive owned modules, checks exact membership in all seven frozen target types, audits the complete lane closure, and ends in `LB02 BUILD_OK`. Development failure logs remain preserved. Only nonfatal style lints from compatibility ports remain.

The final audit covers 472 elaborated declarations. The complete closure is exactly `propext`, `Classical.choice`, and `Quot.sound`. Source scans find no proof placeholders, custom assumptions, or native proof oracles. Lean is 4.33.1 and mathlib is pinned at `0df444a360eaa60ab8c11dca51a86af692955474`.

## Domains and uniformity

All-s transforms retain s>0 and the frozen positive-population domain. The proofs include empty columns, zero/full piles, zero means, empty prefixes and zero-mass prefixes. Every finite prefix theorem permits the alphabets allowed by its contract, including k=0/1; the k=0 feasibility case is proved. The simultaneous error is exactly `2*(K+1)*k^K*exp(-N^epsilon/8)`. For fixed k>=2,T>0,epsilon>0,delta>0, N0 precedes all N and all K<=T log N.

Residual results require b<N, injective prescribed labels and positive prescription probability. The statistic removes prescribed matches and uses the exact reduced mean with population N-b and counts count-used. The factorization theorem handles arbitrary real column tests and every deterministic complement enumeration. The maximal word is selected from the cuts before sampling and before the threshold m; its exponential tail is uniform over this deterministic choice.

## Independent review and provenance

The initial mathematical, Lean representation and missing-hypothesis reviews approved the unchanged contract before proofs. `review_resolution_v1.md` records their comparison. Independent analytic and integration reviews checked the finite recursion, tail constants, concrete substitutions and quantifiers. The one integration elaboration finding was resolved by exposing the canonical sample type, then independently checked. `final_hypotheses_review_v1.md` closes the edge-case audit. No mathematical objection remains.

The initial compatibility provenance remains preserved in `compat_provenance_v1.json`; final checked port hashes and compiler adaptations are recorded in the later `compat_receipt_v1.json` and independently verified in `compat_final_provenance_review_v1.md`, with separate sampling, residual, asymptotic and root proof receipts. Original caches were never imported. New ports and proof files live only under the owned Thinning tree.

## Downstream handoff

Import `RiffleLowerV2.Thinning.Main`. Use `LB02_READY_v1.json` for hashes, export names, logs and the import receipt. The checked output is in `.build/lanes/LB02/lib/lean`. Only LB00/the coordinator may publish these sources into the shared compiled overlay or update umbrella imports for downstream lanes; this task has not modified those shared integration files.
