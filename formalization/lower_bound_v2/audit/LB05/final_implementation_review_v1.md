# LB05 final concrete-closure review v1

Verdict: **PASS for the four frozen LB05 targets.** No extra mathematical hypothesis, missing generic discharge, or numerical/representation defect was found. This review does not assert any other lower-bound lane or final lower-bound theorem.

The reviewer authored the one-column implementation and independently reviewed the selection, empirical interpolation, continuous selection, integer/bridge rounding, and final assembly implemented by the other workers. The initial independent mathematical, representation and missing-hypothesis reviews remain separate artifacts.

## Exact compiled outputs and checks

The final lane log `lane_build_final_v1.log` contains `LB05 BUILD_OK`. A separate pinned-compiler invocation imported `RiffleLowerV2.Witness.Main`, checked each proof against the literal frozen target with an `example`, and printed each transitive axiom closure. See `final_review_declarations_v1.log`.

- `RiffleLowerV2.Witness.oneColumnTilt : RiffleLowerV2.Targets.OneColumnTiltTarget`.
- `RiffleLowerV2.Witness.empiricalTilt : RiffleLowerV2.Targets.EmpiricalTiltTarget`.
- `RiffleLowerV2.Witness.coldWitness : RiffleLowerV2.Targets.ColdWitnessTarget`.
- `RiffleLowerV2.Witness.lB05 : RiffleLowerV2.Targets.LB05Target`.

All four transitive axiom closures are exactly `propext`, `Classical.choice`, `Quot.sound`. The literal ColdWitnessTarget and compiled coldWitness proof were also printed for quantifier inspection. `python3 scripts/lane.py LB05 --check-ready` again returned `LB05 CONTRACT_INPUTS_OK`, verifying unchanged frozen/provenance files and pinned runtime inputs.

## Discharge audit

The one-column target is a proof, not a parameter in the final theorem. It handles every closed-simplex point through explicit zero-support branches. Positive power sum follows from an existing positive simplex coordinate. The proof constructs a normalized tilted simplex, proves the exact entropy identity, derives antitonicity from two finite Gibbs inequalities, and obtains the cost and sharp psi bounds from Shannon entropy bounded by log k. The psi(4) comparison follows from the finite sum-of-squares inequality. No full-support assumption or differentiation at zero is introduced. This is a valid proof route different from the manuscript derivative calculation.

`EmpiricalTilt.lean` has useful generic helpers parameterized by a proof of OneColumnTiltTarget; the exported `empiricalTilt` explicitly supplies the proved `oneColumnTilt`. Its actual dependency closure therefore has no unresolved toolkit assumption. All sums are over `cuts.profile hpos j`. Exact grid sums come from LB00's `empiricalIntegral_grid`; endpoint estimates use the proved clamped finite interpolation and include the actual horizon domains. No TimeLaw or macroscopic transfer estimate is used.

`continuousWitness` derives every generic premise of `variational_pair` and `shorten_selection`. Alpha continuity comes from checked column psi/cost continuity. The outer variational set is nonempty, its values are bounded above by F(3)<=3, and every inner image is bounded below because it is a continuous image of compact [3,4]. The near-supremum point gives all F(alpha)>=7 eta/8. Nonnegative B terms yield beta(s)>=eta/4. The endpoint shortening uses continuous finite integrals, not a temporal regularity assumption. Its theta=4 branch proves the exact integrated no-loss inequality from 2 psi(2)<=psi(4), without restricting the shortening distance.

`roundWitness` receives only the proved continuous selection outputs plus explicit finite threshold bounds. It proves `A(s,S)=beta(s)-beta(S)`, obtains terminal clearance from beta(S)<kappa0 and beta(s)>=eta/4, and only then applies the floor/min/ceiling rounding. Thus natural subtraction `K-bN` is never used as if unsaturated without proof. The bridge capacity and endpoint ordering are proved outputs.

Every rounding error is derived from actual uniform column bounds. With r=2 rho log k and e=log k/log N, the proof establishes the source allowances `r+4e` for J-beta/2 and `5r+20e` for F. The fixed assumptions r<=kappa/100 and e<=kappa/1000 place both below kappa/10. It then derives F>=eta/2, J<=b/2-3 kappa, and the theta=3-or-lower-J clause. The exact entropy identities feed `cold_identity` and `final_margins` to prove all h, H and Gamma inequalities. The mean inequality follows from pointwise a<=I on the prefix and tail and exact additive A, rather than being assumed.

The good bridge columns are constructed using LocalGood on the interior length-rho interval `[u+rho/2,u+3rho/2]`. This interval lies inside the reserved length-at-least-2rho bridge and inside [0,T]. Its left endpoint is strictly greater than u, so all closed-grid columns counted there belong to the required bridge. This validly avoids the possible one-column loss that occurs when starting the counting interval exactly at u. The proof derives two distinct columns from an explicit cardinality lower bound.

## Threshold and quantifier audit

In `coldWitness`, fixed parameters k,T,eta,rho,chiGood,density and their exact frozen assumptions are introduced first. Before N or any cut array, the proof selects:

1. Nr from `exists_logScale_threshold (log k) (16*kappa/1000)`, yielding log k/log N<=kappa/1000.
2. Ng from `exists_logScale_gt (3/(density*rho))`, yielding 3<density*rho*log N using positive density and rho.
3. N0=max Nr Ng, with N0>=2 inherited from Nr.

Only after selecting N0 does the proof introduce N, all actual cuts, the empirical margin, terminal beta, and LocalGood. It derives the exact horizon bound from `horizonDepth_error`, obtains continuous data via `continuousWitness`, and supplies every premise to `roundWitness`. The witness itself is an existential output. N0 actually depends on fewer parameters than permitted; it is independent of the cut array, N-dependent witness data, and any macro profile.

The frozen LB05 budget `2*rho*log k<=kappa/100` is unchanged. The smaller kappa0 budget required by downstream LB09 is not imported as an additional premise. Deterministic/zero columns remain allowed. A wholly deterministic array cannot satisfy the cold terminal beta assumption; mixed degenerate columns are handled directly by the toolkit and interpolation.

## Source and interface correspondence

`eq:repair-global-one-column-bounds` and `eq:repair-two-comparisons` correspond to OneColumn and EmpiricalTilt. The empirical step definitions and exact grid sums match the manuscript section immediately before those equations. `lem:cold-witness` corresponds to continuousWitness, roundWitness and the exact exported coldWitness, with `eq:repair-witness-upper`, `eq:repair-witness-lower`, `eq:repair-witness-geometry`, `eq:repair-witness-collision` and `eq:repair-witness-mean` all present literally in the unchanged WitnessSpec.

Downstream lanes should import `RiffleLowerV2.Witness.Main` after coordinator registration of this lane's checked outputs, and use the already released unchanged v1 contract plus the new LB05 proof receipt. No new contract, assumption or target body is needed.

## Reviewed final source identities

| Module | SHA-256 |
| --- | --- |
| `Continuous.lean` | `d4087979d57d206e092e9c3993ed2356371d4b271b33536b020abf663a305a35` |
| `Empirical.lean` | `7220bb0fcb372ec11eb74a284f0dfeacd9485a1bf0618d3be6612097159072c8` |
| `EmpiricalTilt.lean` | `8b7f95dad4a3df89ee66b887ead0ad4c2b264ac6a209f22cfa83af7c40129647` |
| `Finite.lean` | `f8d3121c1c7e05cec61afd9772d746955006b716720ad0d6c3545e1d59e75e2f` |
| `Main.lean` | `c00990a85054cccc1af82b42096d8547aa770d90391f3429f6792a933c66c731` |
| `OneColumn.lean` | `f139c4b37e6b6492e0e140a535df2c5cdd023e74b998af2fee0d53c50ce951fe` |
| `OneColumnBasic.lean` | `0ee7edc19ffb580282b4aad08477fdd409421f30bb52ddcd408974ecc4fd4f81` |
| `Rounding.lean` | `c8b3b2ee0b8eb897607b7c9f1c2d13e87cd659561a355b75a2912f0e24caf959` |
| `Selection.lean` | `898ed53cc48059604afa7b56c675488bdf39f2dc79b6f64c089bd01a9ba47225` |
