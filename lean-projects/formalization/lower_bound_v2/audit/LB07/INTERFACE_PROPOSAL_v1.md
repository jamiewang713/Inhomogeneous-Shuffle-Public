# LB07 interface proposal v1

Adopt the four existing frozen target types without changes:

- `RiffleLowerV2.ProfileTransfer.genericQuadrature : RiffleLowerV2.Targets.GenericQuadrature`
- `RiffleLowerV2.ProfileTransfer.jointPsiContinuity : RiffleLowerV2.Targets.JointPsiContinuity`
- `RiffleLowerV2.ProfileTransfer.marginTransfer : RiffleLowerV2.Targets.MarginTransferTarget`
- `RiffleLowerV2.ProfileTransfer.profileTransfer : RiffleLowerV2.Targets.ProfileTransferTarget`

No shared addition is proposed. The applicable frozen interface receipt is LB00's `CONTRACT_READY.md`, manifest SHA-256 `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`. Readiness returned `LB07 CONTRACT_INPUTS_OK` before implementation. Independent mathematical, representation, and hypothesis reviews are being recorded separately; this proposal is not their acceptance or a proof receipt.

The selected partition precedes `ScalarIntegrable μ P T`. This predicate has exactly its frozen three clauses: integrability of the selected cell masses, maximal-pile cost, and each psi cost for alpha in [2,4]. The generic observable additionally supplies its own continuity and time-integrability hypotheses. No measurable time kernel, macro J/H integrability, time continuity, or temporal derivative is proposed.

Planned internal implementation: canonical Analysis import; owned and provenance-recorded ports of finite empirical estimates and the old lattice/envelope/quadrature arguments; an explicit complement argument and finite interpolation estimate; bounded nonempty infimum/supremum comparison; ordered parameter assembly. Owned ports create no prerequisite on another first-stage lane and do not alter original sources or definitions.
