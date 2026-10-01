# LB07 quadrature implementation receipt v1

The exact required export is proved and checked:

```lean
RiffleLowerV2.ProfileTransfer.genericQuadrature : RiffleLowerV2.Targets.GenericQuadrature
```

Its statement is the unchanged frozen `Contracts/v1/TransferFinite.lean` definition. The proved error is

    2*T*omega + M*P.cellCount*phi*T + 4*M*rho
      + (4*M*P.cellCount*(T/rho+2)+6*M)/logScale N.

The proof first obtains an absolute sampled estimate by applying the historical one-sided theorem to f and M-f. Spatial continuity plus boundedness proves each spatial integral is well-defined; the explicit temporal integrability premise justifies the complement identity on [r,s]. The cell oscillation is capped at min(omega,M). Probability-measure nonemptiness proves P.cellCount>=1, including the otherwise vacuous k=0 case. The two-sided sampled estimate plus the checked `empiricalIntegral_sample_error` proves the result for the actual step interpolation. The cell-mass integrability premise remains present exactly as frozen; the complement route does not need to use this additional premise.

Fresh port details superseding the abbreviated provenance text in `quadrature_port_provenance_v1.md`: original source hashes are recorded there and were not changed. LatticeCounts, IntegralEnvelope, and GridQuadrature are fresh source ports in the owned namespace `RiffleLowerV2.ProfileTransfer.Compat`. Changes consist of namespace/import replacement, provenance comments, and replacement of method notation by explicit namespace-qualified calls (`BorelPartition.measurableSet_cell`, `cell_mass_bounds`, `sum_cell_mass`, and `AlmostLike.timeCellCount_error`) where namespace relocation requires it. The old proofs are otherwise unchanged. Error contains only the historical quadratureError definition under the owned namespace. No historical file, shared declaration, contract, or build configuration was edited.

Successful command from the package root:

```text
python3 scripts/lane.py LB07 RiffleLowerV2.ProfileTransfer.Quadrature
```

The clean successful build is recorded in `audit/LB07/quadrature_build_v2.log` (`LB07 BUILD_OK`, exit 0). The preceding v1 log records an implementation inference failure and is preserved; it is not a certification record. The successful command freshly rechecks the imported owned ports, Endpoint, and Empirical source against the pinned package environment. The lane build lock has been released.

Local helper exports are `sampledQuadrature` and `quadrature_budget` in the same ProfileTransfer namespace. Downstream import: `RiffleLowerV2.ProfileTransfer.Quadrature`. The coordinator's final aggregate axiom audit should include `genericQuadrature`; this receipt reports successful kernel checking, not an independently executed axiom-closure enumeration.

Checked source hashes:

- `RiffleLowerV2/ProfileTransfer/Compat/LatticeCounts.lean`: SHA-256 `d4cb3be3a72c004c0b266a252fe22c576919f279e0591942f29af4d3da9d80c2`
- `RiffleLowerV2/ProfileTransfer/Compat/IntegralEnvelope.lean`: SHA-256 `2c8b827a7a203c4739c65c3697d5acbcbe6b117fd65ab544810784a92e27b218`
- `RiffleLowerV2/ProfileTransfer/Compat/GridQuadrature.lean`: SHA-256 `bafd48d57bc58c40f3b465e1f981ca8dfbbf12651feaa42f52609a612d8ccf76`
- `RiffleLowerV2/ProfileTransfer/Compat/Error.lean`: SHA-256 `1a0d3dfcf5920eb3f890ef8cefaae4c2d5c47c60ed232b7678cb76e1f9841df6`
- `RiffleLowerV2/ProfileTransfer/Quadrature.lean`: SHA-256 `a4f65d208be27de1e8c8c97673d563d47bada12bb34427a2340147433c0d20f0`
