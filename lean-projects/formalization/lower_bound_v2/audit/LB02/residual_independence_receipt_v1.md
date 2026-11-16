# LB-02 direct residual column independence receipt, v1

Date: 2026-10-01. Import
`RiffleLowerV2.Thinning.Residual.Independence`.

The proved export `RiffleLowerV2.Thinning.residualColumnIndependence` constructs
the exact residual `Cuts k (N-b) K` and states, for every allowed deterministic
complement enumeration and every family of real functions of a residual raw
column, that the conditional expectation of their product is the product of
their expectations under the residual `columnPMF`s. Counts are exactly
`cuts.count j a-usedCount r j a`. Hypotheses are precisely `b<N`, injective
prescribed labels, and positive prescription probability; no extra positivity,
boundedness, or regularity restriction on the column tests is imposed.

The proof first applies the already checked arbitrary residual-array
expectation transport, then applies the finite product expectation identity.
The empty column family is included. This exports independence directly,
in addition to the complete conditional residual law.

The auxiliary `uniform_pi_expect_prod` adapts the elementary six-line proof of
`RiffleLower.uniform_pi_expect_prod` from
`lean-lower-bound/RiffleLower/FixedColumns.lean`, lines 54-62. That historical
source has SHA-256
`f7b9827fb59064ba817bb2f40c778218b6e8b041a0448561cc375dbfbd27018d`.
The current proof uses `PMF.uniformOfFintype` and the checked current
`uniform_expect` adapter, followed by mathlib `Fintype.prod_sum`,
`Finset.prod_div_distrib`, and `Fintype.card_pi`. No old compiled artifact or
old probability-law definition is imported.

The auxiliary product identity explicitly carries `[DecidableEq I]` so the
finite Pi enumeration instance agrees with its caller. The concrete conditional
theorem instantiates it at `Fin K`, which supplies this instance; the exported
residual theorem gains no hypothesis. This resolved an elaboration resource
problem without changing the mathematics. Earlier failed logs are preserved.

Successful command:

```text
python3 scripts/lane.py LB02 RiffleLowerV2.Thinning.Residual.IndependenceCheck
```

The log `audit/LB02/residual_independence_build_v5.log` prints the exact two
exported types, reports standard-only closures `propext`, `Classical.choice`,
`Quot.sound`, and ends with `LB02 BUILD_OK`. The checked module has no reported
warning. It is now imported by the coordinator's `Thinning.Main` source;
the coordinator's final umbrella audit remains a separate receipt.

| Artifact | SHA-256 |
| --- | --- |
| `RiffleLowerV2/Thinning/Residual/Independence.lean` | `0c3214a843a4acd34ee5536876ce871c7df9f77a54616a9ab58fff0e7f5be85b` |
| `RiffleLowerV2/Thinning/Residual/IndependenceCheck.lean` | `a4021bf6dad5126e40200660b904c705ce663810e417c02d80dbabe07a7dbdbc` |
| `audit/LB02/residual_independence_build_v5.log` | `1344a792aa2c5bb4bef6ecc771359821356ab078d62b026470a7e80801cccb08` |
