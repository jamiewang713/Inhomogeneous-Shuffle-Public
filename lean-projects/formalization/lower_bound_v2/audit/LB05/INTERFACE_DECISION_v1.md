# LB05 interface decision, version 1

The mathematical, Lean-representation, and missing-hypothesis reviews independently found the frozen v1 statements compatible with the assigned source. Their detailed reports are stored alongside this decision. No change to shared definitions, hypotheses, conclusions, quantifier order, or exported target names is proposed.

The existing LB00 receipt `audit/LB00/CONTRACT_READY.md` and immutable manifest SHA-256 `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858` are the applicable interface receipt. `python3 scripts/lane.py LB05 --check-ready` returned `LB05 CONTRACT_INPUTS_OK` before proof implementation began.

Required exports remain exactly:

- `RiffleLowerV2.Witness.oneColumnTilt : RiffleLowerV2.Targets.OneColumnTiltTarget`
- `RiffleLowerV2.Witness.empiricalTilt : RiffleLowerV2.Targets.EmpiricalTiltTarget`
- `RiffleLowerV2.Witness.coldWitness : RiffleLowerV2.Targets.ColdWitnessTarget`
- `RiffleLowerV2.Witness.lB05 : RiffleLowerV2.Targets.LB05Target`

All helper definitions live in the owned Witness directory. All concrete empirical integrals, variational margins, cut profiles, local-good premises, and witness specifications remain the frozen definitions. No macroscopic profile or temporal-regularity premise is introduced.

The review specifically validates zero coordinates, deterministic columns, an arbitrarily long tilt-4 backward move, terminal clearance from the beta difference, and the possible loss of one column at a closed interval endpoint. Implementation must prove and discharge each of those obligations. This decision is not a proof-completion receipt.
