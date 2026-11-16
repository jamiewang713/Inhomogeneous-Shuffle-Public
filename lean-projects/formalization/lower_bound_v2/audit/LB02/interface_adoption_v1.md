# LB02 interface adoption v1

This lane adopts all seven frozen v1 target types without changing a hypothesis, constant, conclusion, or quantifier. The governing receipt is `audit/LB00/CONTRACT_READY.md`, manifest SHA256 `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`. The lane readiness command `python3 scripts/lane.py LB02 --check-ready` returned `LB02 CONTRACT_INPUTS_OK` on 2026-10-01.

## Required exports

- `RiffleLowerV2.Thinning.successiveThinning : RiffleLowerV2.Targets.SuccessiveThinning`
- `RiffleLowerV2.Thinning.prefixTails : RiffleLowerV2.Targets.PrefixTails`
- `RiffleLowerV2.Thinning.allPrefixConcentration : RiffleLowerV2.Targets.AllPrefixConcentration`
- `RiffleLowerV2.Thinning.prefixFailureUniform : RiffleLowerV2.Targets.PrefixFailureUniform`
- `RiffleLowerV2.Thinning.residualLaw : RiffleLowerV2.Targets.ResidualLaw`
- `RiffleLowerV2.Thinning.hypergeometricTransform : RiffleLowerV2.Targets.HypergeometricTransform`
- `RiffleLowerV2.Thinning.maximalMeanIdentity : RiffleLowerV2.Targets.MaximalMeanIdentity`

## Source and invariants

`lem:successive-thinning-tail` requires the one-step transform for every real s>0, exact uniform fixed-size columns, backward affine recursion, Bernstein constant 1/4, lower-tail constant (1-log 2)/2, and the X<2 factor 2. Positive population M is explicit. Empty column sets use X=M, Q=1. No row-independence assumption is permitted.

`cor:iterated-hypergeom` includes every prefix length 0..K and all words, including zero masses. The finite probability error is exactly 2(K+1)k^K exp(-N^epsilon/8), for N>=2 and epsilon>0. Uniform threshold order is k>=2, T>0, epsilon>0, delta>0, then N0, then every N>=N0, K<=T log N and deterministic cuts.

`prop:largest-prefix` contributes only canonical maximal-word choice, mean/exponent identity and its exponential count tail. The physical-law/run/TV assembly belongs to LB10 and requires LB01's law bridge.

Residual conditioning requires b<N, injective prescribed labels, and positive prescription probability. The population is N-b and every digit count loses its prescribed occurrences. An arbitrary injective exhaustive enumeration of the unprescribed labels is allowed. The resulting product law must be proved; naming a residual distribution is insufficient.

## Supporting declarations, not contract changes

Proof modules may expose ordinary proved lemmas for finite expectations, all-s hypergeometric estimates, abstract transform-to-tail consequences, actual prefix transforms, residual specializations, polynomial union bounds and the maximal-word exponential tail. These are implementation helpers in the owned `RiffleLowerV2/Thinning/` tree. They are not new assumptions or proposition-valued target substitutions. Their final exact compiled signatures will be recorded in the delivery inventory. No shared addition or contract alteration is proposed.

## Provenance and work allocation

Old source is read-only. Any reused `lean/Shuffle` source must be copied into the owned namespace/import tree, carry original and port hashes, and be checked using the pinned 4.33.1 compiler. Old compiled caches are forbidden. Concrete PMF bridges remain proof obligations even after a FiniteLaw proof compiles.

Independent mathematical, representation and hypothesis reports are collected alongside this file. Proof work starts only after their findings are compared and resolved in `review_resolution_v1.md`; the existing LB00 receipt covers the unchanged target types.
