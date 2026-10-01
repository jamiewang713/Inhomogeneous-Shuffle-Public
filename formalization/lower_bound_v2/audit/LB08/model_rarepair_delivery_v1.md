# LB08 actual rare-pair estimate v1

`RiffleLowerV2.Occupancy.rare_pair_relative_uniform` is proved in `Occupancy/RarePair.lean`. Its assumptions are precisely fixed c,C>0, the logarithmic horizon, selected-pile lower bounds for both distinct words, and rarity of the first mean `N*wordMass w <= tau N`. The other mean is unrestricted. The constants and threshold precede N,k,K, counts, words, and their means.

The exact result has the shape

```text
∀ c C > 0, ∃ D > 0, ∃ N0, 2 <= N0 ∧
  ∀ N >= N0, ∀ k K, K <= C log N ->
  ∀ cuts w v, w != v -> selected-pile bounds for w,v -> mean(w) <= tau N ->
  |P(Aw ∩ Av) - P(Aw) P(Av)| <= D tau(N) P(Aw) P(Av).
```

No generic moment, conditional-collision, or independence premise remains in this public result. It directly uses the proved `uniform_marginal`, `conditionalCollisionStability`, original one-word moment input, forcing positivity/weighted expansion, and rare-regime algebra.

If J is the positive constant extracted from the actual conditional theorem at deletion budget 3, the proof chooses L=2(J+8), H=2L+1, and final D=16H. A finite threshold ensures `tau<=1/16`, `H*tau<=1/2`, the second/third factorial error is at most tau, every requested pile has at least three cards, and 3<=N^(1/5). The final threshold is a sum of the four input thresholds and 3, chosen before varying data. The present conditional implementation supplies J=64, but the proof does not depend on unfolding that internal value.

The proof keeps the two small parameters separate: the original rare-marginal denominator bound uses tau<=1/4 and gives p_w>=mu_w^2/4; the final weighted pair comparison uses H*tau. Original and conditional marginal estimates give forcing stability relative to the actual second marginal, even when it is extremely small. The factorial-weighted stability then combines with the original moment error. No tail error is divided by an uncontrolled rare marginal.

Additional proved helpers in the same module:

- `weighted_rare_sandwich`: multiply the pointwise second/third factorial sandwich by an arbitrary event indicator and average under the canonical finite PMF.
- `weighted_moment_relative`: combine a relative moment comparison with relative forcing stability, yielding coefficient 2L+1.
- `eventual_rare_pair_budgets`: all numerical forcing, moment and enlarged-error conditions with a uniform threshold.

Successful lane command:

```text
python3 scripts/lane.py LB08 RiffleLowerV2.Occupancy.RarePair
```

`audit/LB08/model_rarepair_build_v1.log` ends in `LB08 BUILD_OK`, without warnings or errors. The lane command rebuilt the actual imported LB08 dependency chain in its assigned overlay. Development logs preserve an initial spacing/parser issue and a final predicate-function simplification issue; `model_rarepair_readonly_dev03.log` records the corrected proof's clean read-only compile before the successful lane publication.

The statement/axiom probe is `model_rarepair_check_v1.lean`; it exited zero. Its log contains the complete actual theorem type and records only `propext`, `Classical.choice`, and `Quot.sound` in every helper and public theorem closure. Source scope was limited to `Occupancy/RarePair.lean` and new `model_rarepair_*` audit files. No shared contract, upstream source, dependency cache, historical receipt, or sibling-owned source was modified.
