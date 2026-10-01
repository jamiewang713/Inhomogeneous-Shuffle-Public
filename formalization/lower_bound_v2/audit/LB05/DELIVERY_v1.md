# LB05 completion and downstream receipt, version 1

All LB05 obligations are proved against the unchanged frozen v1 contract. The complete finite empirical witness is an output: the final theorem constructs its grid endpoints, tilt, bridge length, two good bridge columns, and every inequality in `WitnessSpec`. There are no pending LB05 mathematical or Lean dependencies and no new hypotheses.

## Exact required exports

Import:

```lean
import RiffleLowerV2.Witness.Main
```

The compiled declarations have exactly these types, without additional binders:

```lean
RiffleLowerV2.Witness.oneColumnTilt : RiffleLowerV2.Targets.OneColumnTiltTarget
RiffleLowerV2.Witness.empiricalTilt : RiffleLowerV2.Targets.EmpiricalTiltTarget
RiffleLowerV2.Witness.coldWitness : RiffleLowerV2.Targets.ColdWitnessTarget
RiffleLowerV2.Witness.lB05 : RiffleLowerV2.Targets.LB05Target
```

`EXPORTS_v1.md` and `public_exports_v1.json` give the exact types and source locations of all 87 public declarations. `compiled_declarations_v1.json` records all 131 elaborated Witness declarations, including private and generated proof dependencies. The theorem types above refer to the original, unmodified proposition definitions in `Contracts/v1/WitnessGeometry.lean`; the audit checks actual proof declarations rather than merely checking those propositions.

## Source correspondence and dependency ledger

The authoritative manuscript is `time_inhomogeneous_riffle_shuffle_unified_article.tex`, SHA-256 `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`. Its assigned source label is `lem:cold-witness`.

| Source obligation | Checked implementation | Status |
|---|---|---|
| `eq:repair-global-one-column-bounds`: zero coordinates, cost/entropy bounds, sharp psi bound | `OneColumn.lean`: `tiltedCost_bounds`, `tiltedEntropy_bounds`, `psi_sharp_bounds`, `oneColumnTilt` | Proved |
| Continuity and monotonicity in the tilt | `continuousOn_tiltedCost`, `continuousOn_tiltedEntropy`, `continuousOn_psi`, `tiltedCost_antitone` | Proved |
| Exact entropy/cost identities | `tiltedEntropy_identity`, `H_identity`, `cold_identity` | Proved |
| `eq:repair-two-comparisons` | `maxCost_le_tiltedCost`, `psi_two_le_maxCost`, `psi_four_ge_two`; integrated comparison lemmas | Proved |
| Finite empirical step interpolation and exact grid sums | Frozen `columnFraction_grid`, `empiricalIntegral_grid`; new `columnFraction_sum`, `empiricalIntegral_const` | Proved |
| Uniform endpoint continuity and Lipschitz bounds | `empiricalIntegral_endpoint_bound`, `continuous_empiricalIntegral`, specialized J/H/B bounds; `empiricalTilt` | Proved |
| Real infimum/supremum selection | `variational_pair`: nonempty triangle, bounded inner images, bounded outer image, strict near-supremum extraction | Proved |
| Tilt 3, tilt 4, and intermediate-value cases; shortening | `select_tilt`, `shorten_selection`, `F_move_eq`, `continuousWitness` | Proved from actual columns |
| Terminal clearance and source rounding | `terminal_clearance`, `rounded_indices`, `roundWitness` | Proved |
| Two good bridge columns | `good_bridge_columns` instantiated inside `roundWitness` | Proved from actual `LocalGood` |
| `eq:repair-witness-upper`, `eq:repair-witness-lower` | `endpoint_error_algebra`, `rounding_margins`, `roundWitness` | Proved with exact constants |
| `eq:repair-witness-geometry`, `eq:repair-witness-collision` | `final_margins`, exact empirical entropy identities, `roundWitness` | Proved |
| `eq:repair-witness-mean` | `a <= I` integrated over the two actual intervals and exact additivity in `roundWitness` | Proved |
| Uniform eventual finite witness | `coldWitness` in `Main.lean` | Proved; threshold precedes cuts |
| All assigned obligations together | `lB05` | Proved |

The generic empirical helper premises are all discharged by `oneColumnTilt`. The generic selection and rounding premises are all discharged by the concrete finite-column proofs. No witness-existence premise, macroscopic `TimeLaw`, almost-profile assumption, scalar-integrability condition, or temporal-regularity premise enters `coldWitness`.

## Numerical and quantifier audit

The final theorem has the frozen order: fixed `k >= 2`, positive `T, eta, rho, chiGood, density`, and the bridge budget `2*rho*log k <= kappa eta/100`; then `exists N0 >= 2`; then every `N >= N0` and every horizon cut array; then the empirical margin, terminal beta, and local-good premises; then the constructed witness.

`Main.lean` takes the maximum of two thresholds chosen using only `k, eta, rho, density`. They ensure

```text
log k / log N <= kappa eta / 1000,
3 < density * rho * log N.
```

The original constants remain `kappa eta = eta/1000` and `kappa0 eta = min(kappa eta/100,1/1000)`. The first threshold charges the errors to the fixed margins:

```text
abs(Delta F) <= 5*(2*rho*log k) + 20*log k/log N <= 0.07*kappa,
abs(Delta(J-b/2)) <= 2*rho*log k + 4*log k/log N <= 0.014*kappa.
```

Both are at most `kappa/10`. Before clipping, the beta difference proves strict clearance `s0+2*rho+2/log N < S_N`. Thus natural subtraction in `K_T-ceil(2*rho*log N)` never invalidates the endpoint ordering. The tilt-4 branch uses `B4 >= 2 B2` and imposes no bound on its backward displacement.

For bridge extraction, the proof applies the existing every-interval `LocalGood` hypothesis to `[u+rho/2,u+3*rho/2]`. This interval lies inside the reserved bridge, and its left endpoint is strictly after `u`. This valid choice avoids the possible one-column loss from a closed interval beginning exactly at `u`; it does not strengthen the hypothesis. The resulting indices satisfy the exact zero-based `WitnessSpec` bounds.

## Build and trust audit

Run from `formalization/lower_bound_v2`:

```text
python3 scripts/lane.py LB05 --check-ready
python3 scripts/lane.py LB05 RiffleLowerV2.Witness.Main
```

Results: `LB05 CONTRACT_INPUTS_OK` and warning-free `LB05 BUILD_OK`. The successful final build is preserved in `lane_build_final_v1.log`. The pinned runtime is Lean 4.33.1 and pinned mathlib commit is `0df444a360eaa60ab8c11dca51a86af692955474`. All new modules compile into `.build/lanes/LB05/lib/lean`; no historical toolchain cache is imported.

The separate `Check_v1.lean` audit was compiled with warnings treated as errors against that lane output. `compiled_audit_v1.log` ends `AUDIT_OK`. It verifies exact target specialization and recursively inspects every new declaration's axiom closure. The union is exactly:

```text
propext
Classical.choice
Quot.sound
```

There are no proof placeholders, custom axioms, or native proof oracles. `verification_v1.json` records source hashes, import lists, exact target proofs, build/audit logs, and an empty pending-obligations list.

## Independent review findings and resolutions

- `math_review_v1.md` checks the source argument, especially all three tilt cases, terminal clearance, and numerical margins. No false target or missing hypothesis was found.
- `representation_review_v1.md` verifies the exact frozen Lean representations. The missing cached analytic imports were resolved by copying only needed proof text into the owned module and recompiling against the canonical definitions. `one_column_provenance_v1.md` records the original file hash and ported declarations.
- `hypotheses_review_v1.md` tests zero and deterministic columns, near-terminal witnesses, and closed-interval bridge endpoints. No additional assumption was required.
- `implementation_review_v1.md` independently audits the initial helper snapshots. Later final snapshots are covered by `final_implementation_review_v1.md` and its independent compiler log `final_review_declarations_v1.log`.
- The final implementation review passes with no unresolved findings. It verifies that the concrete proofs discharge every generic premise and that `N0` is uniform in the cuts.

The one-column proof uses finite Gibbs comparisons to establish antitonicity on `[1,infinity)`, avoiding differentiation at zero coordinates. All support and normalization facts are proved, and the sharp psi bound follows from Gibbs plus the entropy bound. This is a proved alternative to the source's derivative explanation, with the same definitions and conclusions.

## Downstream integration

LB05 consumes the unchanged LB00 v1 receipt, manifest SHA-256 `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`. The full lane entry point is `RiffleLowerV2.Witness.Main`. More selective imports are `Witness.OneColumn`, `Witness.EmpiricalTilt`, `Witness.Continuous`, `Witness.Rounding`, and `Witness.Finite` under the `RiffleLowerV2` prefix.

The coordinator can register the completed lane with its serialized package build before downstream lanes import it from the shared cache. No shared file, target definition, Lake configuration, umbrella import, old audit, or old freeze was modified. Other lanes and the eventual full lower-bound theorem remain outside this receipt's scope.
