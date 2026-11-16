# LB-02 residual prefix transport and bound adapters, v1

Date: 2026-10-01. Import
`RiffleLowerV2.Thinning.Residual.Prefix`.

This additive module preserves the separately certified exact residual-law
source and receipt. It defines:

- `prescribedPrefixCount r w`: the number of prescribed row words matching `w`.
- `residualPrefixCount r w omega`: `prefixCount w omega` minus that number.
- `residualPrefixMass cuts r w`: the product, over the prefix columns, of
  `(cuts.count j w_j-usedCount r j w_j)/(N-b)`.
- `residualPrefixMean cuts r w`: `(N-b)*residualPrefixMass cuts r w`.
- `rowArrayPrefixCount`: the direct count on an arbitrary row array.

The following exports are proved without any concentration-theorem assumption:

- `residualPrefixCount_eq_restriction`: on the prescribed-word event, the
  natural subtraction is exactly the count restricted to any allowed
  deterministic complement enumeration. Thus truncation outside that event
  cannot alter a conditional expectation or probability.
- `residualPrefixMass_eq` and `residualPrefixMean_eq`: the actual residual
  `Cuts` mass and mean are exactly the displayed subtraction formulas.
- `residualPrefixExpect` and `residualPrefixProbability`: transport any real
  function or event of this count to the actual residual fixed-count law. Both
  retain `b<N` explicitly and quantify over every allowed enumeration.
- `existsComplementEnumeration`: an injective prescribed row list admits such
  a deterministic complement enumeration, chosen from the prescription alone.

Two additional proved adapters carry **explicit unconditional theorem inputs**:

```lean
residualPrefixTails_of_prefixTails
    (hT : RiffleLowerV2.Targets.PrefixTails) ...

residualPrefixTransform_of_prefixTransform
    (hT : forall cuts hN w s hs, <the two concrete prefix transform comparisons>) ...
```

Their exact elaborated types are in the successful log. The first adapter returns
all three manuscript bounds, with the unchanged constants `4`,
`chernoffConstant=(1-log 2)/2`, and `2`, using `residualPrefixMean`. The second
returns both all-positive-parameter comparisons with the residual binomial
population exponent `N-b` and the exact residual exponential mean. Both require
injective prescribed rows, positive prescription probability, and `b<N`.
No lower bound on the conditioning probability is imposed.

The adapter inputs must be discharged by the coordinator's proved concrete
prefix theorems. This receipt does not treat an adapter with `hT` as proof that
its unconditional input, or the entire LB-02 lane, is complete. Once those
inputs are available, applications of these adapters provide the requested
conditional specializations without an added mathematical hypothesis.

Successful command from `formalization/lower_bound_v2`:

```text
python3 scripts/lane.py LB02 RiffleLowerV2.Thinning.Residual.PrefixCheck
```

Log: `audit/LB02/residual_prefix_build_attempt_2.log`, ending in
`LB02 BUILD_OK`. The earlier failed diagnostic log is preserved separately.
The successful build reports one harmless unused `sampleRow` simp-argument
warning. The five checked transport/adapter declarations have closure exactly
`propext`, `Classical.choice`, and `Quot.sound`. An explicit source scan found no
forbidden proof tokens in either substantive residual module. All work stayed
inside the owned residual files and audit paths.

| Artifact | SHA-256 |
| --- | --- |
| `RiffleLowerV2/Thinning/Residual/Prefix.lean` | `e858e223a9a2d19fafadff543c57bcd009b67cb3ebe4fb81b3ebad12369f9510` |
| `RiffleLowerV2/Thinning/Residual/PrefixCheck.lean` | `97ce8b1e82d3accec4a2a25d14fe7fe1b36695449a8ea6c4d4d56e6fc0029b33` |
| `audit/LB02/residual_prefix_build_attempt_2.log` | `6df0d7cb4eb14e39df26ecbbf409ff360d4d244342689f6f59ea5222f60118bf` |

No mathematical or API obstacle remains in this subtask. The outstanding
integration step is the explicit discharge of the adapters' unconditional
inputs and import into the lane entry point, both owned by the coordinator.
