# LB11 parameters implementation: independent review v1

Verdict: PASS. The four numerical helper proofs preserve the frozen constants and require no unannounced mathematical assumption. They are sufficient for the proposed direct largest/cold endpoint assembly. This report certifies the parameters module only, not the later macroscopic theorem or upstream coordinator readiness.

Reviewed source: `RiffleLowerV2/MacroscopicLower/Parameters.lean`.

Source SHA-256: `ac7da881e475df4b5820a240b36739c0a50b8a496f7830636d17de7419c14def`.

The module imports only `RiffleLowerV2.Shared.Empirical`. The owner's `audit/LB11/parameters-dev03.log` records `LB11 BUILD_OK`. I additionally re-elaborated the source independently with Lean 4.33.1 and `-DwarningAsError=true`, reading the LB11 overlay and writing no output/cache files. The command exited with code 0 and no diagnostics:

```text
LEAN_PATH='<package>/.build/lanes/LB11/lib/lean' '<Lean 4.33.1>/bin/lean' -DwarningAsError=true RiffleLowerV2/MacroscopicLower/Parameters.lean
```

## Exact arithmetic

1. `transferAccuracy_spec`: for eta > 0, both arguments of the minimum are strictly positive, so `e = min (kappa0 (eta/2)/10) (eta/100) / 2` is positive and strictly smaller than each argument. The strictness is supplied by halving a positive minimum, not incorrectly inferred from the weak minimum bounds. This choice is mathematically identical to `min (k0/20) (eta/200)` in my pre-proof review.

2. `coldMargin_scale`: the exact expansion is `kappa0 (eta/2) = min (eta/200000) (1/1000)`. The proof uses positivity and the left minimum inequality, so it applies for every positive eta with no unspoken small-eta restriction.

3. `bridgeCeiling_spec`: k >= 2 implies log k > 0. The ceiling is `(k0/100)/(2 log k)`, which is strictly positive. Multiplying `rho <= ceiling` by the positive denominator yields `2 rho log k <= k0/100`. No positivity assumption on rho is needed for this algebraic helper; the endpoint separately supplies the required `0 < rho`. Hence the helper is stronger than the endpoint's use, without weakening its hypotheses.

4. `small_beta_forces_cold`: the selected lower sides of the two absolute-value bounds are exactly the needed directions. They imply

   - `lambda0 <= betaFinite + e + d < k0 + 5e/4`, since `d <= e/4`;
   - `lambdaFinite >= lambda1 - (13/2)e - 14d >= lambda1 - 10e`.

   With `k0 <= eta/200000` and `e < eta/100`, the first bound is strictly below eta. The `max` assumption then forces `eta <= lambda1`. Finally `lambdaFinite >= eta - 10e > 9eta/10 > eta/2`, which is stronger than the exported non-strict conclusion. The proof correctly returns both `lambda0 < eta` and `eta/2 <= lambdaFinite`.

The helper intentionally has no lower bound on d. This is logically sound: only its upper bound is needed by either derivation, and the actual application has `d = log k / logScale N >= 0` once `N >= 2`. No inconsistent or target-restating premise is being used.

## Assembly compatibility

Using the existing proved `ProfileTransfer.transferThreshold_spec (log k)` with tolerance `e` gives precisely the helper input `d <= e/4`; the resulting error constants are `5e/4` and `10e`. The final branch threshold remains exactly `kappa0 (eta/2)`. A common maximum of transfer, logarithmic, largest-word, and cold thresholds continues to give uniformity over all cut arrays, including alternating branches.

The numerical declarations are generic lemmas, not assumed endpoint evidence. The later endpoint must instantiate the two bounds from actual LB07 `ProfileMarginErrors`, provide the actual macro maximum premise, and discharge the local-good/cold-parameter conditions to the actual LB10 theorem. The parameters file changes none of these obligations and changes no shared contract.

No revision requested for this source hash. A final independent review should inspect the macroscopic theorem after implementation and expanded-type/axiom output after compilation.
