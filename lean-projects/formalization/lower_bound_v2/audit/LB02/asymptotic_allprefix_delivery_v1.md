# LB-02 simultaneous-prefix helper delivery v1

`RiffleLowerV2.Thinning.allPrefixConcentration_of_prefixTails` proves

```lean
(htails : RiffleLowerV2.Targets.PrefixTails) :
  RiffleLowerV2.Targets.AllPrefixConcentration
```

The exact stochastic premise is supplied as a proved input by the root assembly. This conditional helper alone is not an unconditional concentration theorem and does not complete the lane.

The proof uses every member of the actual sigma prefix type, so the empty prefix and all zero-mass prefixes are included. `prefix_card_exact` proves cardinality `∑ n : Fin (K+1), k^n.val`. The polynomial bound `(K+1)*k^K` is proved for `k≥1`; positive feasible cuts with `K>0` force `k≥1`, while `K=0` is handled directly. Thus the frozen theorem's `k=0` and `k=1` domains remain unchanged.

`prefixMean_nonneg` is a direct consequence of the deterministic product definition. `prefix_bernstein_exponent` proves exactly `A/8 ≤ [A(sqrt μ+1)]²/[4(μ+A(sqrt μ+1))]` for `μ≥0,A≥1`. Each fixed-prefix failure event is bounded by `2 exp(-N^ε/8)`, then the finite union bound and exact prefix cardinality give the frozen `prefixFailure`. No independence of rows or ancestor-family restriction enters this helper.

Imports: only `Contracts.v1.ModelThinning` and `RiffleLowerV2.Shared.Adapters`. The small finite probability monotonicity and union-bound lemmas are private, so this module does not wait for another lane-local probability module. All arguments are ordinary checked finite-sum proofs.

Read-only source verification passed with no warnings in `asymptotic_allprefix_readonly_v2.log`; the later final lane build and axiom audit are the authoritative compiled checks, recorded separately.

The proper locked lane build `python3 scripts/lane.py LB02 RiffleLowerV2.Thinning.AllPrefixes` succeeded (`asymptotic_allprefix_build_final.log`). The read-only audit against its compiled artifact printed all seven public types and axiom closures in `asymptotic_allprefix_axioms.log`, each exactly `[propext, Classical.choice, Quot.sound]`. Content hashes and the explicit conditional status are recorded in `asymptotic_allprefix_receipt_v1.json`.
