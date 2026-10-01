# LB07 Spatial implementation receipt, v1

`RiffleLowerV2/ProfileTransfer/Spatial.lean` is implemented and compiled with
Lean 4.33.1 in the LB07 private lane. Its only imports are
`Contracts.v1.TransferFinite` and the already registered canonical
`RiffleTimeProfile.Analysis`. The read-only dependency check
`python3 scripts/check_dependency_receipt.py LB06-v1` returned
`LB06-v1 DEPENDENCIES_OK` before implementation.

Successful module build:

```
python3 scripts/lane.py LB07 RiffleLowerV2.ProfileTransfer.Spatial
```

Output: `LB07 BUILD_OK`, recorded in `spatial-build-v2.log`.
`spatial-build-v1.log` records only an earlier lane-lock conflict, not a Lean
error. No dependency build or shared file mutation was performed.

The exact public types are checked and printed in `spatial-check-v1.log` by
`SpatialCheck_v1.lean`, run against the LB07 private output with warnings as
errors. All eleven public declarations have transitive axiom closure exactly
`[propext, Classical.choice, Quot.sound]`:

* `continuous_prob`, `continuous_pileMax`, `continuous_maxCost`;
* `continuous_psi` for α∈[2,4];
* `jointPsiContinuity : Targets.JointPsiContinuity`;
* `integrable_of_continuous_bounded`, `integrable_maxCost`, `integrable_psi`;
* `scalar_integral_bounds`, `profileMaxCost_bounds`, `profilePsi_bounds`.

All names are under `RiffleLowerV2.ProfileTransfer`. The profile bounds are
`0≤profileMaxCost≤log k` and `0≤profilePsi(α)≤4log k`; the latter is the
already proved canonical bound, sufficient for LB07's monotone terminal
comparison and for choosing the quadrature tolerance. It is not advertised
as the sharper source inequality `(α-1)log k`.

The continuity proofs expose arguments previously local to the checked
canonical `TimeProfile.exists_regular_partition` proof: continuity of finite
maxima and of coordinate real powers, with positivity of α handling zero
coordinates, followed by positivity of the power sum before logarithmic
continuity. The new direct `ContinuousOn` statement proves the exact frozen
joint-continuity target. No probability-kernel or temporal-continuity premise
is introduced. Spatial integrability uses continuous measurability plus the
explicit finite pointwise bound. The profile bounds are pointwise in time
and therefore apply to every historical `TimeLaw` without asserting any
temporal integrability.

Source/implementation SHA-256 values are preserved in
`spatial-source-provenance-v1.json`. The canonical Analysis source is used
verbatim from the coordinator's compatible receipt; no old cache is imported.
Source correspondence is the continuity/bounded-observable part of
`lem:lower-profile-transfer`. Quadrature, empirical endpoint interpolation,
margin transfer, and complete ordered parameter assembly remain separate
lane obligations; this receipt does not claim those completed.
