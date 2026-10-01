# LB-02 uniform error and maximal-word proof delivery v1

Both exact frozen targets are proved and compiled: `RiffleLowerV2.Thinning.prefixFailureUniform : Targets.PrefixFailureUniform` and `RiffleLowerV2.Thinning.maximalMeanIdentity : Targets.MaximalMeanIdentity`. No shared definitions, contracts, old packages, or manuscript were changed.

## Uniform convergence

`UniformError.lean` proves the explicit envelope

`prefixFailure N k K ε ≤ 2 (T+1) N^(1+T log k) exp(-N^ε/8)`

for `N,k≥2`, `T>0`, and `K≤T log N`. This pays the existing polynomial prefix count cost and yields a threshold depending only on `k,T,ε,δ`, uniformly over every permitted `N,K` and all cut arrays. The proof establishes stretched-exponential domination by substitution into mathlib's proved `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`, then composes with natural casts. It does not assume a chosen depth sequence.

Public helpers are `prefixFailure_le_envelope`, `tendsto_power_mul_stretchedExp`, and `prefixFailureEnvelope_tendsto`; exact elaborated types are in `asymptotic_axioms.log`.

## Canonical maximal word

`MaximalWord.lean` selects the least member of the nonempty set of maximizing digits in each column. The word is chosen from deterministic cuts before sampling. `exists_canonicalMaxWord` and `canonicalMaxWord_mean` require only `N>0`, so even the feasible `k=0,K=0` case is covered. `maximalMean_eq_rpow_beta` requires `N≥2` and proves the exact empirical horizon identity using the checked grid-integral adapter and positivity of every maximal pile fraction. The final target has exactly its frozen `k≥2,N≥2` domain.

These proofs establish the deterministic word and its mean; the exponential probability tail remains the root agent's specialization of the stochastic estimates. No permutation or total-variation conclusion is claimed here.

## Verification and provenance

Successful command from the package directory:

```text
python3 scripts/lane.py LB02 RiffleLowerV2.Thinning.MaximalWord RiffleLowerV2.Thinning.UniformError
LB02 BUILD_OK
```

The command used the locked LB-02 overlay and is recorded in `asymptotic_build_final.log`. The separate read-only Lean audit `asymptotic_check.lean` was run under the same lane lock against those compiled artifacts. Its log prints all eight public declaration types and their axiom closures, each exactly `[propext, Classical.choice, Quot.sound]`. Earlier failed development logs are retained and are not certification evidence.

These are original lane-local proofs using the canonical shared model and pinned mathlib, not ports from historical Lean caches. `UniformError` imports `Contracts.v1.ModelThinning` and pinned `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`; `MaximalWord` imports `Contracts.v1.AssemblyInputs` and `RiffleLowerV2.Shared.Adapters`. The latter contracts expose `Targets.deckPos`. The verified hashes of outputs and logs are in `asymptotic_receipt_v1.json`.

Downstream import both `RiffleLowerV2.Thinning.UniformError` and `RiffleLowerV2.Thinning.MaximalWord`, or the root-owned main module once it imports them.
