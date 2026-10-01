# LB05 independent representation review v1

Reviewed the assigned prompt, current manuscript `lem:cold-witness` and its empirical cost definitions, frozen Contracts/v1, LB00 release, Base/Analysis/AnalyticParameters, and legacy Cold. No implementation is certified by this review.

## Verdict and exact interface

The frozen v1 interface faithfully expresses the assignment. No extra mathematical premise or shared-definition amendment is needed. Required exports are exactly:

- `RiffleLowerV2.Witness.oneColumnTilt : RiffleLowerV2.Targets.OneColumnTiltTarget`
- `RiffleLowerV2.Witness.empiricalTilt : RiffleLowerV2.Targets.EmpiricalTiltTarget`
- `RiffleLowerV2.Witness.coldWitness : RiffleLowerV2.Targets.ColdWitnessTarget`
- `RiffleLowerV2.Witness.lB05 : RiffleLowerV2.Targets.LB05Target`

The last type is the conjunction of the first three targets. `Contracts.v1.WitnessGeometry` contains their literal types; `Shared.Geometry.WitnessSpec` contains the full concrete conclusion. Target definitions are propositions, not proofs. None of the four required proof declarations existed at review start.

`ColdWitnessTarget` orders fixed `k,T,eta,rho,chiGood,density` and their positive/budget conditions before `exists N0`, then quantifies every `N >= N0` and every finite cut array. It assumes exactly the empirical margin, terminal beta bound and `LocalGood`; no witness, TimeLaw, transfer estimate or temporal regularity occurs. `rho > 0` is explicit. The LB05 budget is `2*rho*log k <= kappa eta/100`; the separate LB09 target deliberately uses `kappa0 eta/100`. Preserve this distinction.

## Representation checks

- `Simplex` includes zero coordinates. Tilt uses actual real powers; cost and entropy have explicit zero branches. Prove support equivalence for positive tilt before removing those branches. In particular, never use log/rpow identities at an unproved positive coordinate.
- `empiricalIntegral` is an explicit finite sum of differences of clamped column fractions, divided by log N. It is the intended continuous antiderivative of the actual columns, with zero extension. Every scientific use has `N >= 2`; the general total definition is not evidence at N=0 or N=1.
- Lean column `j` corresponds to manuscript column `j.val+1`. At grid endpoints the interval `(a/L,b/L]` is exactly `a <= j.val < b`. LB00 already proves `columnFraction_grid` and `empiricalIntegral_grid`; no new shared adapter is necessary.
- `lambda1` uses real `sSup` of real `sInf` on the actual triangle and [3,4]. Its definitions alone do not supply boundedness or nonemptiness. For the proof establish inner image nonemptiness (alpha=3), lower boundedness by uniform finite costs, outer nonemptiness ((0,0)), and upper boundedness (indeed inner values <= F(3) <= 3). The initial point with all F >= 7 eta/8 can be obtained directly from strict near-supremum approximation and `csInf_le`, without attainment or swapping sup/inf.
- `ColdWitnessData` contains natural endpoints, natural bridge length and a real tilt. `WitnessSpec` includes the exact ceiling, endpoint ordering and sum bound `mu + bridgeLength <= K`, two distinct good columns, [3,4], every displayed numerical margin, and the terminal beta premise. Thus it does not merely package an assumed witness.
- Bridge lower index `mu <= gL.val` is correct. `LocalGood` counts closed time endpoints, so using [u,u+rho] can include the single preceding column (time u). Charge its possible loss, or use an interior rho interval justified inside the bridge. Do not silently identify the closed count with the half-open bridge count.
- A theta=4 shortening can have arbitrarily large displacement; the valid protection is integrated `2*psi(2) <= psi(4)`, not a displacement bound. Near-terminal birth must be protected by `A(s,S)=beta(s)-beta(S)` before taking natural subtraction/clipping.

## Proven versus pending inputs

LB00 compiled Base, Ambient and FixedCountModel plus shared adapters under Lean 4.33.1/mathlib 0df444a360eaa60ab8c11dca51a86af692955474. `python3 scripts/lane.py LB05 --check-ready` succeeded during this review with `LB05 CONTRACT_INPUTS_OK`.

Base provides simplex probabilities, maximum positivity, normalized cuts, logScale positivity and horizon floor error. Shared provides empirical self/additivity and exact grid sums. These are available in the frozen checked closure.

Analysis source contains genuine proofs of `powerSum_pos`, `powerSum_le_one`, `maxCost_bounds`, coarse `psi_bounds`, and `finite_gibbs`; its full tilt toolkit is absent. Continuity of psi is only local to `exists_regular_partition`, not an exported declaration. In particular no existing theorem supplies tilt monotonicity, entropy identity, entropy/cost bounds, or the sharp psi bound requested here.

Analysis and AnalyticParameters have no registered olean in the LB00 cache. Their source toolchain is compatible (4.33.1), but direct lane imports fail until the coordinator registers/rebuilds them. Either request an additive dependency registration with provenance, or port the small required proofs into owned Witness files with exact source hashes. Do not copy another package cache. `exists_logScale_threshold` is a proved useful source helper, but importing all AnalyticParameters brings irrelevant first-moment modules; a documented small port is preferable.

Legacy `RiffleLower.Cold` uses Lean 4.19.0 and is outside the new build PROJECTS. Its `cold_exponent_identity` is a genuine ring identity, not a witness existence theorem. Reprove the one-line polynomial identity against frozen finite definitions or port with provenance; do not import its old olean. Legacy sorting/collision theorems do not discharge this lane.

## Build/receipt recommendation

Lane entry point is `RiffleLowerV2.Witness.Main`, built with `python3 scripts/lane.py LB05 RiffleLowerV2.Witness.Main` from lower_bound_v2. This limits output to `.build/lanes/LB05/` and rejects unregistered upstream imports. Coordinator alone owns shared dependencies, umbrella and frozen manifests. LB00 receipt `audit/LB00/CONTRACT_READY.md` and manifest hash `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858` suffice for unchanged v1 proofs; no new contract freeze is needed for proved owned helper lemmas.

The LB00 axiom audit reports only propext, Classical.choice and Quot.sound. That does not certify newly ported proofs or the future final witness; audit the actual new declaration closure separately after compilation.
