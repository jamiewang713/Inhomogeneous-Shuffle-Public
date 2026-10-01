# LB04 finite MGF machinery delivery v1

The owned module `RiffleLowerV2.Ascent.MGF` is compiled, with no warnings, and exports the exact frozen `RiffleLowerV2.Ascent.bernoulliMGF : RiffleLowerV2.Targets.BernoulliMGF`. Its other seven declarations are proved analytic helpers, not substitutes for the pending concrete graph specialization.

## Checked exports

All names below have namespace `RiffleLowerV2.Ascent`. Exact elaborated types are recorded by the successful `#check` run in `mgf_axioms_v1.log`.

- `bernoulli_mgf`: universe-polymorphic finite PMF indicator bound for every real t, exponent t²/8.
- `bernoulliMGF`: the exact frozen target.
- `one_class_mgf`: given a finite family of indicators and its centered-exponential product-expectation factorization, bounds the centered-sum MGF by exp(u²|s|/8).
- `expect_mul_sq_le`: finite PMF Cauchy–Schwarz for arbitrary real f,g, with PMF weights retained.
- `exp_markov`: P(t≤X) ≤ exp(-ut) E exp(uX), for u>0 and arbitrary real t.
- `parity_mgf`: two class-sum MGF bounds imply the combined MGF bound exp(u²(B0+B1)/4), with no independence between classes.
- `subgaussian_tails`: the all-real bound E exp(uX)≤exp(u²B/4), B,t>0, gives both weak one-sided probabilities ≤exp(-t²/B).
- `two_class_indicator_concentration`: a pointwise decomposition X=c+sum(s0) indicators+sum(s1) indicators, the two exact within-class exponential factorization identities, positive M,t, and |s0|+|s1|≤M give the exact two weak tails about E X bounded by exp(-t²/M).

The final wrapper handles |s0|+|s1|=0 separately by proving X constant; it does not divide by the empty-boundary count. With a positive count it centers by exact finite linearity, applies the two class bounds and Cauchy–Schwarz, uses positive and negative Chernoff parameters, and weakens the denominator to M. No boundary-cardinality hypothesis, integer-M hypothesis, M≤N hypothesis, or shuffle-law assumption was introduced.

## Source correspondence and provenance

All eight exports implement analytic steps of manuscript `lem:permutation-bd`. Bernoulli centering uses the pinned mathlib `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` and its all-real `mgf_le`, specialized to a finite discrete PMF and the range [0,1]. Both finite measurability and all indicator range bounds are discharged inside the proof. The shared `expect_eq_integral` identifies exactly the frozen expectation. Weighted Cauchy–Schwarz uses `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` with pointwise equality of the weighted squares. Exponential Markov and both tail constants are proved in the owned module from the checked owned finite PMF helpers.

The SubGaussian import was added only after reading `audit/LB00/LB04_DEPENDENCIES_READY_v1.md`. Its pinned source hash and transitive axiom checks are in that receipt. The module imports only `RiffleLowerV2.Ascent.FiniteProbability` and `Mathlib.Probability.Moments.SubGaussian`; the former supplies the frozen contract and shared adapter transitively. No old cache was copied or shared file edited.

## Verification

Successful serialized command:

```text
python3 audit/LB04/compile_lane.py RiffleLowerV2.Ascent.MGF
```

Successful warning-free log: `build-20261001T155339600217Z.log`. Both additive dependency receipts were checked by the dispatch path and passed. A separate read-only compiler check, serialized using the same `compile-dispatch.lock`, imported the compiled module and ran `#check` and `#print axioms` for every listed declaration; source `mgf_check_v1.lean`, log `mgf_axioms_v1.log`, exit status 0. All eight axiom sets are exactly `[propext, Classical.choice, Quot.sound]`. The source has no prohibited proof tokens.

## Remaining specialization obligations

The root implementation must prove the concrete component-sort decomposition, construct component-index parity classes, identify their combined count, and discharge each exact factorization identity using the proved joint relative-order law. The generic factorization hypotheses are legitimate intermediate independence consequences; they are not asserted as established for graph boundaries by this module. The root can then apply `two_class_indicator_concentration` with c equal to the retained graph-edge count and M at least |H|. Expectation comparison, scan and asymptotic test remain separate lane obligations.
