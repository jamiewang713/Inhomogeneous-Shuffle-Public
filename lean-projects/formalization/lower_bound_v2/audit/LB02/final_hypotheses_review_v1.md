# LB-02 final edge-case and missing-hypotheses review, v1

Date: 2026-10-01. Scope: independent review of the coordinator's final
`Process`, `Prefixes`, `Main`, `AllPrefixes`, `UniformError`, and `MaximalWord`
sources against the exact frozen targets and assigned manuscript labels.
Relevant sampling, coordinate, recursion, and tail dependencies were read as
well. This reviewer previously implemented the residual modules; this report
independently audits their concrete assembly and the other listed modules,
rather than claiming a second independent authorship review of those residual
proofs themselves. No proof file was edited as part of this final review.

## Final verdict and checked evidence

**Approved. No missing hypothesis, false conclusion, changed constant,
unjustified quantifier exchange, or unresolved edge case was found.** The
formerly generic stochastic inputs are now discharged by concrete theorems in
the actual shared fixed-count PMF model.

The initially inspected `main_build_v1.log` failed on a Lean sample-type
conversion in the prefix transform. The repaired source was then inspected;
the change explicitly identifies the same canonical sample space and count,
and changes no hypothesis or conclusion. `main_build_v2.log` passed. The final
assembly additionally imports the proved direct residual independence module.

The authoritative final evidence is
`audit/LB02/final_build_and_axioms_v1.log`, which ends with `LB02 BUILD_OK`.
Its SHA-256 is
`590a42b3a91b2236f1b1269c0c988aa074c1337d82f926032c62e15f82ab4b86`.
The reviewed `Thinning.Check` source explicitly type-checks all seven required
exports against their frozen target types and traverses every public/private
Thinning declaration for axiom closure. The final log contains all seven exact
target declarations, the concrete conditional wrappers, the maximal-word tail,
and direct residual independence. Its complete recorded axiom union is only
`propext`, `Classical.choice`, and `Quot.sound`.

The current compiled artifacts for all six principal reviewed modules are newer
than their source. A direct hash comparison also confirmed all 43 entries in
the frozen `Contracts/v1/SHA256.json` remain unchanged. Historical pre-proof
ledgers and failed build logs are not treated as current completion evidence.

## Exact target and domain comparison

| Export | Final comparison |
| --- | --- |
| `successiveThinning` | Exactly `Targets.SuccessiveThinning`: `M>0`, all sizes at most `M`, and every `s>0`; both transform comparisons retained. |
| `hypergeometricTransform` | Exactly `Targets.HypergeometricTransform`, including `x<=M`, `m<=M`, `M>0`, and the formerly missing `s>1` range. |
| `prefixTails` | Exactly `Targets.PrefixTails`: all actual prefixes under `fixedCountPMF`, `N>0`, all `t>0`, and all three numerical bounds. |
| `allPrefixConcentration` | Exactly `Targets.AllPrefixConcentration`, including every `k`, `N>=2`, every positive epsilon, and the unchanged `prefixFailure`. Its former `PrefixTails` input is supplied by the proved concrete theorem. |
| `prefixFailureUniform` | Exactly `Targets.PrefixFailureUniform`; the threshold is chosen before varying `N` and `K`. |
| `residualLaw` | Exactly `Targets.ResidualLaw`, including positive conditioning probability, injective prescribed labels, `b<N`, exact count subtraction, and every complement enumeration. |
| `maximalMeanIdentity` | Exactly `Targets.MaximalMeanIdentity`, including the deterministic smallest-maximizer tie rule and exact `N^beta` identity at the empirical horizon. |

## Degenerate cases and representation checks

- **Positive population:** no final process/prefix/residual tail silently drops
  `M>0`, `N>0`, or `b<N`. Some internal finite-law identities are valid on a
  larger domain, but the public frozen statements retain their prescribed
  domains.
- **Empty sequence:** the recursion's zero-column case is the deterministic
  count of the initial set. With the full initial label set, `X=M`, empty
  product `Q=1`, and mean `M`. No nonempty-column premise appears.
- **Zero mean and endpoint fractions:** ratio and product bounds are
  non-strict; affine positivity explicitly allows `q=0` and `q=1`. Bernstein
  divides by `mu+t`, which is positive for `mu>=0,t>0`, and never by `mu`.
- **Empty prefix:** prefix coordinate equality uses exactly the existing
  coordinates; all unused suffix factors and sets are neutral. The empty
  prefix therefore has mass one and count `N`, also when `K=0`.
- **Zero-mass prefix:** it remains in every public quantifier. The separate
  `prefixCount_eq_zero_of_mass_zero` proves its count is pointwise zero in every
  valid matrix; no almost-sure exception or positive-pile restriction is used.
- **Alphabet `k=0`:** with `N>0`, any existing column would contradict its
  total count. `prefix_card_le_of_cuts` handles `K=0` first and derives the
  contradiction otherwise. It does not invoke the false unrestricted bound
  `sum_{r<=K}0^r <= (K+1)0^K` for positive `K`. The nonvacuous case has exactly
  one empty prefix and `0^0=1`.
- **Alphabet `k=1`:** the finite targets retain this domain; their prefix count
  bound uses only `1<=k`. All columns are deterministic, and the unique prefix
  at each length has count and mean `N`. The asymptotic target's separate
  `2<=k` premise is exactly its frozen premise.
- **Concrete law:** digit-fiber sampling is proved under the actual uniform
  `ColumnAssignments` law. Recursive finite coordinate integration is applied
  to that law. The count bridge and neutral suffix product identify the exact
  shared `prefixCount` and `prefixMass`; no row-independence claim or replacement
  row model is used.

## Constants and simultaneous concentration

The final analytic and concrete statements retain

`2 exp(-t^2/(4(mu+t)))`,
`exp(-((1-log 2)/2)*mu)`, and `2 exp(-mu/2)`.

The square-root threshold is exactly
`N^epsilon*(sqrt(N*lambda_w)+1)`. The checked deterministic substitution gives
the exponent lower bound `N^epsilon/8`. The complement of the simultaneous
non-strict event is contained in the union of the corresponding non-strict
tail events, so the strict/non-strict event conventions have the correct
direction.

`prefix_card_exact` counts the sigma type of variable-length prefixes as
`sum_{r=0}^K k^r`; no suffix multiplicity is counted. Its upper bound yields
exactly `2*(K+1)*k^K*exp(-N^epsilon/8)`. Every length is included, and neither
ancestor-family membership nor positive mass is assumed.

The asymptotic proof bounds this unchanged finite error by the common envelope
`2*(T+1)*N^(1+T*log k)*exp(-N^epsilon/8)`. This envelope is only a proof device;
it does not replace the exported finite constant. It tends to zero for fixed
`k,T,epsilon`, independently of `K` and the cut array. The chosen threshold is
`max N0 2` and is placed before `forall N>=N0, forall K`.
Dependence on `k,T,epsilon,delta` is permitted; dependence on `K`, cuts, the
chosen prefix, or a sampled matrix is absent. No unsupported uniformity in
unbounded `k` or in a bounded residual population is asserted.

## Residual specialization and independence

`residualPrefixTransform` in `Main.lean` directly applies
`residualPrefixTransform_of_prefixTransform` to the proved `prefixTransform`.
`residualPrefixTails` in that module applies the analogous adapter to the proved
`prefixTails`. The final compiled types contain no leftover abstract stochastic
premise.

The remaining count is the full count minus the number of prescribed words
matching the prefix, with exactness proved on the prescription event. Its
mass uses every relevant subtracted digit count divided by `N-b`; its mean is
`(N-b)` times that mass. Thus neither the original population/mean nor the full
count is silently retained. All constants are independent of the prescription
and its positive probability. Complement enumerations are deterministic and
quantified before sampling.

The final imported `residualColumnIndependence` additionally exports the exact
conditional product-expectation identity for arbitrary real raw-column test
functions and the residual column PMFs. It has the same prescription domain and
exact residual counts. Independence is therefore directly available to
downstream callers, in addition to following from the complete residual law.

## Maximal-word scope

The canonical maximizing word is selected from the deterministic cuts before
the probability event, with the smallest digit breaking each tie. Its mean is
the product of the column maxima times `N`; at `N>=2` the exact exponent adapter
identifies this with `N^beta` at the empirical horizon, without time regularity
or local-good-column assumptions.

`maximalWordTail` bounds `P(wordCount w<m)` whenever `m<=mu_*/2`, with precisely
`exp(-chernoffConstant*mu_*)`. Its broader allowance of natural `m=0,1` is
harmless and stronger than needed for the downstream `m>=2` run test.
No increasing-run or physical-law/TV conclusion is claimed here. The remaining
law bridge and permutation/run calculation belong to LB-01/LB-10 as required
by the assignment, rather than constituting an omitted LB-02 conclusion.

## Reviewed source identities

| Module | SHA-256 |
| --- | --- |
| `Process` | `19ed3d26b23d8cafb7807fcceef48ccc3e70c5cd43579543ec8aeea4aebb111b` |
| `Prefixes` | `3186a217fc234148f3ec2993c396f0492aad18670b75120e6ce5068fbfdb4ff2` |
| `Main` | `20c7050ff4e6bb2093703aaf8dfde634f82050252303ed90811897785d43281d` |
| `AllPrefixes` | `50a1a63987193154d00b721f0f040afe589864db72e838a512ad8858ebe0527a` |
| `UniformError` | `1370a1242fc236a697a1c3e107a869f843bc5581a960ca1e1b7716e3f3bfaa52` |
| `MaximalWord` | `fa720aceb1935b1f86926eccfc0a7901177fb945c5b33d2ee8a7bce1b24329b4` |

No unresolved edge-case or missing-hypothesis finding remains for this final
checked snapshot. This is LB-02 certification, not certification of the full
lower-bound theorem or downstream lanes.
